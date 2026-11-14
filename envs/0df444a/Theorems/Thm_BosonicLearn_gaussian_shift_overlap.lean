-- Prove2me | Theorems.Thm_BosonicLearn_gaussian_shift_overlap
-- name    : BosonicLearn.gaussian_shift_overlap
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T21:28:23.809198+00:00
-- url     : https://prove2.me/theorems/e46d240e-a00c-4140-8048-635692633fc3
-- title:
--   Two Gaussian measures $\mathcal N(\mu,T)$, $\mathcal N(\mu+Tw,T)$ have a common part of mass $\ge1-\sqrt{w^TTw}/\sqrt{2\pi}$
-- statement:
--   A total-variation bound for two Gaussian measures with the same covariance.
--
--   Let $T$ be a positive semidefinite real $d\times d$ matrix, $\mu\in\mathbb R^d$ and $w\in\mathbb R^d$. There is a measure $\kappa$ on $\mathbb R^d$ with
--
--   $$
--   \kappa\le\mathcal N(\mu,T),\qquad\kappa\le\mathcal N(\mu+Tw,\,T),\qquad\kappa(\mathbb R^d)\ \ge\ 1-\frac{\sqrt{w^{T}Tw}}{\sqrt{2\pi}} .
--   $$
--
--   Equivalently, the total variation distance of the two Gaussians is at most $\sqrt{w^TTw}/\sqrt{2\pi}$ (the exact value is $2\Phi(\tfrac12\sqrt{w^TTw})-1$). For invertible $T$ and a shift $\delta=Tw$, $w^TTw=\delta^TT^{-1}\delta$.
--
--   Role. Classical counterpart of Lemma 18 of the paper: it controls the part of a mean shift that can be absorbed in the mixing measure of a classical Gaussian state (`BosonicLearn.lemma_18_classical`).
--
--   **Formalization Note** The shift is taken in the range of $T$, so no inverse is needed and singular $T$ is allowed. The measures are Mathlib's `multivariateGaussian` on `EuclideanSpace ℝ ι`; the statement is purely classical probability.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Overlap of two Gaussian measures with the same covariance.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 18 (first-moment perturbation), Eq. (204), p. 60 (classical counterpart: two Gaussians with equal covariance and
shifted means are close in total variation).

Let `T` be a positive semidefinite real matrix, `μ` a vector and `w` a vector. The Gaussian measures `N(μ, T)` and
`N(μ + Tw, T)` have a common part of mass at least `1 − √(wᵀTw)/√(2π)`: there is a measure `κ` with `κ ≤ N(μ, T)`,
`κ ≤ N(μ + Tw, T)` and `κ(ℝᵈ) ≥ 1 − √(wᵀTw)/√(2π)`. Equivalently their total variation distance is at most
`√(wᵀTw)/√(2π)`.

**Formalization Note.** The shift is taken in the range of `T` (`Tw`), so that no inverse of `T` is needed;
for invertible `T` and shift `δ`, `wᵀTw = δᵀT⁻¹δ`. The measures are Mathlib's `multivariateGaussian`. -/
theorem gaussian_shift_overlap {ι : Type} [Fintype ι] [DecidableEq ι] (μ : EuclideanSpace ℝ ι)
    (T : Matrix ι ι ℝ) (hT : T.PosSemidef) (w : ι → ℝ) :
    ∃ κ : Measure (EuclideanSpace ℝ ι),
      κ ≤ multivariateGaussian μ T ∧
      κ ≤ multivariateGaussian (μ + WithLp.toLp 2 (T *ᵥ w)) T ∧
      1 - Real.sqrt (w ⬝ᵥ (T *ᵥ w)) / Real.sqrt (2 * Real.pi) ≤ (κ Set.univ).toReal := by sorry

end BosonicLearn
