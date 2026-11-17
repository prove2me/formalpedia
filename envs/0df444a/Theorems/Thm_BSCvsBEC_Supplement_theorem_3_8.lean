-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_3_8
-- name    : BSCvsBEC.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:39:24.320438+00:00
-- url     : https://prove2.me/theorems/235fc35c-718a-4b61-831d-a9f5e3d135ff
-- title:
--   Theorem 3.8 — $P_{\mathrm{guess}}(\mathrm{PSC}_\theta,\mathcal C)=2^{-k}\big(\sum_v\sqrt{P_V(v)}\big)^2$
-- statement:
--   Let $\mathcal C\le\mathbb F_2^n$ be a binary linear code of dimension $k$ with generator matrix $G$ (a parity-check matrix of $\mathcal C^\perp$), let $0\le\theta\le\pi/2$ and $\rho=\cos\theta$. Let $X$ be uniform on $\mathcal C$ and sent through $\mathrm{PSC}_\theta$ (any pair of unit vectors $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ with $\langle\omega_0|\omega_1\rangle=\cos\theta$). Let $P_V$ be the distribution of the syndrome $V=GY^\perp$, where $X^\perp$ is uniform on $\mathcal C^\perp$ and $Y^\perp=\mathrm{BSC}_p(X^\perp)$ with $p=(1-\cos\theta)/2$. Then
--   $$P_{\mathrm{guess}}(\mathrm{PSC}_\theta,\mathcal C)=2^{-k}\Big(\sum_{v\in\mathbb F_2^k}\sqrt{P_V(v)}\Big)^2,$$
--   with $P_{\mathrm{guess}}$ the optimum over all POVMs. This is equivalent to Rengaswamy–Pfister [RP21b, Theorem 15].
--
--   Differences from the source:
--   - encoding: F₂ → ZMod 2 (definitionally Fin 2, so the published IsPSCPair, pscVec, becState apply); reason: a field structure is needed for linear codes; same set
--   - encoding: a linear code 𝒞 of dimension k with generator matrix G (Gᵀ a parity-check matrix of 𝒞⊥) → a matrix G ∈ F^{k×n} with u ↦ Gᵀu injective, 𝒞 = codeOf G; reason: every k-dimensional code with every generator matrix arises this way, and conversely
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ (IsPSCPair θ ω); reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: P_guess as max over POVMs (eq. (17)) → sSup over every POVM indexed by the input alphabet (pGuess); reason: the set of values is nonempty and bounded above by 1 for a pmf and density matrices, so the supremum is the maximum's value
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 3.8, eq. (74), p.15 (setting of Proposition 3.7, p.15)

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_Supplement_pErr
import Definitions.Def_BSCvsBEC_Supplement_syndromePMF

open scoped Matrix

namespace BSCvsBEC.Supplement

/-- **Theorem 3.8 (p.15; equivalent to Rengaswamy–Pfister [RP21b, Theorem 15]).** In the setting of
Proposition 3.7 with `q = 2`, if `0 ≤ θ ≤ π/2` and `ρ = cos θ`, then
`P_guess(PSC_θ, 𝒞) = 2^{−k} (∑_{v∈F₂^k} √P_V(v))²` (eq. (74)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 3.8, eq. (74), p.15, in the setting of Proposition 3.7, p.15.

**Formalization Note.** `F₂ = ZMod 2` (definitionally `Fin 2`, so the published `IsPSCPair` and
`pscVec` apply). `G ∈ F₂^{k×n}` with `u ↦ Gᵀu` injective is a generator matrix of the `k`-dimensional
code `𝒞 = codeOf G`, equivalently a parity-check matrix of `𝒞⊥`. `X` is uniform on `𝒞` (`codePMF`), sent
through `PSC_θ` for any pair `ω` with `IsPSCPair θ ω`; `P_guess` is the supremum over all POVMs.
`P_V = syndromePMF G (cos θ)`: `X⊥` uniform on `𝒞⊥` through `BSC_p`, `p = (1 − cos θ)/2`, `V = G Y⊥`. -/
theorem theorem_3_8 {k n : ℕ} (G : Matrix (Fin k) (Fin n) (ZMod 2))
    (hG : Function.Injective (Gᵀ.mulVec)) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : BSCvsBEC.IsPSCPair θ ω) :
    pGuess (codePMF (codeOf G)) (fun x => BSCvsBEC.ketbra (BSCvsBEC.pscVec ω x)) =
      ((2 : ℝ) ^ k)⁻¹ * (∑ v, Real.sqrt (syndromePMF G (Real.cos θ) v)) ^ 2 := by sorry

end BSCvsBEC.Supplement
