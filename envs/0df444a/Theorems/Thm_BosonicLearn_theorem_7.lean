-- Prove2me | Theorems.Thm_BosonicLearn_theorem_7
-- name    : BosonicLearn.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:30:19.076521+00:00
-- url     : https://prove2.me/theorems/9ff6dade-1da1-4a11-8338-dbead4711840
-- title:
--   Theorem 7 — one-sided relative covariance bound $\tfrac12\|\rho(0,\Sigma')-\rho(0,\bar\Sigma)\|_1\le\Delta_{\mathrm{rel}}/(2\sqrt{2\gamma_-})$
-- statement:
--   Let $\bar\Sigma$ be the covariance matrix of an $n$-mode Gaussian state whose symplectic eigenvalues are all at least $\nu_->\tfrac12$, and let $\Sigma'\succeq\bar\Sigma$ be another covariance matrix. Define
--
--   $$\gamma_-=1-\frac{1}{2\nu_-},\qquad \Delta_{\mathrm{rel}}=\big\|\bar\Sigma^{-1/2}(\Sigma'-\bar\Sigma)\bar\Sigma^{-1/2}\big\|_{\mathrm F}.$$
--
--   Then
--
--   $$\tfrac12\big\|\rho(0,\Sigma')-\rho(0,\bar\Sigma)\big\|_1\le\frac{1}{2\sqrt{2\gamma_-}}\,\Delta_{\mathrm{rel}} .$$
--
--   The prefactor depends only on the gap $\nu_--\tfrac12$ and not on $n$; this is what makes heterodyne tomography of warm states cost $O(n^2/\varepsilon^2)$.
--
--   Differences from the source:
--   - encoding: symplectic eigenvalues of Σ̄ all at least ν₋ → every z in the complex spectrum of ΩΣ̄ (Ω = [[0, I], [−I, 0]]) has |z| ≥ ν₋; reason: that spectrum is {±iν_j} (p. 55); no Williamson construction is needed
--   - encoding: Δ_rel = ‖Σ̄^{-1/2}(Σ′ − Σ̄)Σ̄^{-1/2}‖_F → √Tr(Σ̄⁻¹(Σ′ − Σ̄)Σ̄⁻¹(Σ′ − Σ̄)); reason: equal: the squared Frobenius norm of the symmetric matrix
--   - encoding: covariance matrices Σ′, Σ̄ with the Gaussian states ρ(0, Σ′), ρ(0, Σ̄) → zero-mean states given with IsGaussianState for Σ′ and Σ̄; reason: a covariance matrix is valid exactly when such a state exists
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 7, Eqs. (184)–(185), p. 55

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Theorem 7 (One-sided relative covariance bound).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 7, Eqs. (184)–(185), p. 55: "Let Σ̄ be an n-mode covariance matrix whose symplectic eigenvalues are
all at least ν₋ > 1/2, and let Σ′ be another covariance matrix satisfying Σ′ ⪰ Σ̄. Define γ₋ := 1 − 1/(2ν₋),
Δ_rel := ‖Σ̄^{−1/2}(Σ′ − Σ̄)Σ̄^{−1/2}‖_F. Then ½‖ρ(0, Σ′) − ρ(0, Σ̄)‖₁ ≤ (1/(2√(2γ₋))) Δ_rel."

For zero-mean Gaussian states `ρ(0, Σ′)` and `ρ(0, Σ̄)` with `Σ′ ⪰ Σ̄` and all symplectic eigenvalues of `Σ̄` at least
`ν₋ > ½`, the trace distance is at most `Δ_rel / (2√(2γ₋))`.

**Formalization Note.** "Covariance matrix" means the covariance of a state, so `Σ′, Σ̄` are given as covariances
of Gaussian states. The symplectic eigenvalues are read off the spectrum of `ΩΣ̄`, `Ω = [[0, I],[−I, 0]]`
(grouped order, Eq. (2)), which is `{±iν_j}` (p. 55); the hypothesis is `|z| ≥ ν₋` for every `z` in that complex
spectrum. `Δ_rel² = Tr(Σ̄⁻¹(Σ′−Σ̄)Σ̄⁻¹(Σ′−Σ̄))`, the squared Frobenius norm of `Σ̄^{−1/2}(Σ′−Σ̄)Σ̄^{−1/2}`. The radical in
the prefactor covers `2γ₋` (rendered p. 55; Eq. (216)). -/
theorem theorem_7 {n : ℕ} (ρ' ρbar : State (Occupation (Fin n)))
    (S' Sbar : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h' : IsGaussianState ρ' 0 S') (hbar : IsGaussianState ρbar 0 Sbar) (νm : ℝ) (hνm : 1 / 2 < νm)
    (hsympl : ∀ z ∈ spectrum ℂ ((Matrix.fromBlocks 0 1 (-1) 0 * Sbar).map (fun x : ℝ => (x : ℂ))),
      νm ≤ ‖z‖)
    (hord : (S' - Sbar).PosSemidef) :
    traceDist ρ'.coefficients ρbar.coefficients ≤
      ENNReal.ofReal (1 / (2 * Real.sqrt (2 * (1 - 1 / (2 * νm)))) *
        Real.sqrt (Sbar⁻¹ * (S' - Sbar) * Sbar⁻¹ * (S' - Sbar)).trace) := by sorry

end BosonicLearn
