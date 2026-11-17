-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_3_9
-- name    : BSCvsBEC.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:40:13.036679+00:00
-- url     : https://prove2.me/theorems/95a5d0ac-ad9a-4705-bf7b-9c28019b8b5c
-- title:
--   Theorem 3.9 — $P_{\mathrm{guess}}(\mathrm{qPSC}_\theta,\mathcal C)=\frac1K\big(\sum_v\sqrt{P_V(v)}\big)^2$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $\mathcal C\le\mathbb F_q^n$ a linear code of dimension $k$ with generator matrix $G$ (a parity-check matrix of $\mathcal C^\perp$), $K=q^k$, and let $0\le\theta\le\pi/2$, $\rho=\cos\theta$. Let $X$ be uniform on $\mathcal C$ and sent through $\mathrm{qPSC}_\theta$, and let $P_V$ be the distribution of the syndrome $V=GY^\perp$, where $X^\perp$ is uniform on $\mathcal C^\perp$ and $Y^\perp=\mathrm{qSC}_p(X^\perp)$ with $p=\frac{q-1}q(1-\rho)$. Then
--   $$P_{\mathrm{guess}}(\mathrm{qPSC}_\theta,\mathcal C)=\frac1K\Big(\sum_{v\in\mathbb F_q^k}\sqrt{P_V(v)}\Big)^2,$$
--   with $P_{\mathrm{guess}}$ the optimum over all POVMs.
--
--   Together with Proposition 3.7, the right side is $\|T_\rho f_{\mathcal C^\perp}\|_{1/2}$, which links PSC decoding to the reverse Samorodnitsky inequality.
--
--   Differences from the source:
--   - encoding: a linear code 𝒞 of dimension k with generator matrix G (Gᵀ a parity-check matrix of 𝒞⊥) → a matrix G ∈ F^{k×n} with u ↦ Gᵀu injective, 𝒞 = codeOf G; reason: every k-dimensional code with every generator matrix arises this way, and conversely
--   - reading: some fixed pure states (|ω_x⟩) in the q-dimensional 𝒴 with ⟨ω_x|ω_x'⟩ = cos θ for x ≠ x' → every such family of unit vectors in ℂ^q (IsQPSCOn θ ω); reason: the page fixes an arbitrary such family; the statement is required for each one
--   - encoding: P_guess as max over POVMs (eq. (17)) → sSup over every POVM indexed by the input alphabet (pGuess); reason: the set of values is nonempty and bounded above by 1 for a pmf and density matrices, so the supremum is the maximum's value
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 3.9, eq. (75), p.15 (setting of Proposition 3.7, p.15)

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_Supplement_pErr
import Definitions.Def_BSCvsBEC_Supplement_syndromePMF

open scoped Matrix

namespace BSCvsBEC.Supplement

/-- **Theorem 3.9 (p.15).** In the setting of Proposition 3.7, write `K = q^k`. If `0 ≤ θ ≤ π/2` and
`ρ = cos θ`, then `P_guess(qPSC_θ, 𝒞) = (1/K) (∑_{v∈F_q^k} √P_V(v))²` (eq. (75)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 3.9, eq. (75), p.15, in the setting of Proposition 3.7, p.15.

**Formalization Note.** Every finite field `F = F_q`; `G ∈ F_q^{k×n}` with `u ↦ Gᵀu` injective is a
generator matrix of the `k`-dimensional code `𝒞 = codeOf G` (a parity-check matrix of `𝒞⊥`). `X` is
uniform on `𝒞`, sent through `qPSC_θ` for any family `ω` with `IsQPSCOn θ ω` (unit vectors in `ℂ^q`,
pairwise inner products `cos θ`); `P_guess` is the supremum over all POVMs.
`P_V = syndromePMF G (cos θ)` with `p = ((q − 1)/q)(1 − cos θ)`. -/
theorem theorem_3_9 {F : Type} [Field F] [Fintype F] [DecidableEq F] {k n : ℕ}
    (G : Matrix (Fin k) (Fin n) F) (hG : Function.Injective (Gᵀ.mulVec))
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : F → EuclideanSpace ℂ (Fin (Fintype.card F))) (hω : IsQPSCOn θ ω) :
    pGuess (codePMF (codeOf G)) (fun x => BSCvsBEC.ketbra (BSCvsBEC.pscVec ω x)) =
      (((Fintype.card F : ℝ) ^ k)⁻¹) *
        (∑ v, Real.sqrt (syndromePMF G (Real.cos θ) v)) ^ 2 := by sorry

end BSCvsBEC.Supplement
