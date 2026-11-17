-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_3_10
-- name    : BSCvsBEC.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:41:12.06601+00:00
-- url     : https://prove2.me/theorems/34e71068-b143-4aab-bac1-55ac542fee0a
-- title:
--   Theorem 3.10 — $P_e(\mathrm{PSC}_\theta,\mathcal C)\le P_e(\mathrm{BEC}_\lambda,\mathcal C)$ for linear codes, $\lambda\ge\cos^2\theta$
-- statement:
--   Let $\mathcal C\le\mathbb F_2^n$ be a linear code and let $0\le\theta\le\pi/2$. For $X$ uniform on $\mathcal C$,
--   $$P_e(\mathrm{PSC}_\theta,\mathcal C)\ \le\ P_e(\mathrm{BEC}_\lambda,\mathcal C)\qquad\text{provided }\lambda\ge\cos^2\theta,$$
--   where $\mathrm{PSC}_\theta$ uses any pair of unit vectors $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ with $\langle\omega_0|\omega_1\rangle=\cos\theta$, and $P_e=1-P_{\mathrm{guess}}$ is the error of the optimal POVM (MAP decoding on the erasure channel).
--
--   This is the linear-code version of Theorem 3.1, obtained from Theorems 3.3 and 3.8 and Proposition 3.6.
--
--   Differences from the source:
--   - encoding: F₂ → ZMod 2 (definitionally Fin 2, so the published IsPSCPair, pscVec, becState apply); reason: a field structure is needed for linear codes; same set
--   - encoding: X uniform on the linear code 𝒞 → codePMF 𝒞 for a ZMod 2-subspace 𝒞; reason: same instances
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ (IsPSCPair θ ω); reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: provided λ ≥ cos²θ → cos²θ ≤ λ ≤ 1; reason: λ is the erasure probability of BEC_λ, defined only for λ ∈ [0, 1]
--   - encoding: P_guess as max over POVMs (eq. (17)) → sSup over every POVM indexed by the input alphabet (pGuess); reason: the set of values is nonempty and bounded above by 1 for a pmf and density matrices, so the supremum is the maximum's value
--   - encoding: MAP decoding on BEC_λ → pGuess of the diagonal cq states becState λ x = diag(∏ᵢ W(yᵢ|xᵢ)); reason: the page's eq. (17) treats a classical channel as a cq channel with diagonal states; the optimal POVM value equals MAP decoding
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 3.10, eq. (80), p.16

import Mathlib
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_Supplement_pErr
import Definitions.Def_BSCvsBEC_Supplement_syndromePMF

namespace BSCvsBEC.Supplement

/-- **Theorem 3.10 (p.16).** Let `𝒞 ≤ F₂ⁿ` be a linear code and let `0 ≤ θ ≤ π/2`. Then
`P_e(PSC_θ, 𝒞) ≤ P_e(BEC_λ, 𝒞)` provided `λ ≥ cos²θ` (eq. (80)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 3.10, eq. (80), p.16.

**Formalization Note.** `F₂ = ZMod 2` (definitionally `Fin 2`); `𝒞` is any `ZMod 2`-subspace of `F₂ⁿ` and
`X` is uniform on it (`codePMF 𝒞`). The PSC states are `|ω_x⟩⟨ω_x|` for any pair with `IsPSCPair θ ω`,
the BEC states are `becState λ x` (MAP decoding); `P_e = 1 − P_guess` with `P_guess` the supremum over
all POVMs. `λ` ranges over `[cos²θ, 1]`. -/
theorem theorem_3_10 {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : BSCvsBEC.IsPSCPair θ ω)
    (lam : ℝ) (hl : Real.cos θ ^ 2 ≤ lam) (hl1 : lam ≤ 1) :
    pErr (codePMF C) (fun x => BSCvsBEC.ketbra (BSCvsBEC.pscVec ω x)) ≤
      pErr (codePMF C) (becState lam) := by sorry

end BSCvsBEC.Supplement
