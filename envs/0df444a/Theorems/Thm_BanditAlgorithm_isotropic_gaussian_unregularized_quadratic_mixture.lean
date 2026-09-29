-- Prove2me | Theorems.Thm_BanditAlgorithm_isotropic_gaussian_unregularized_quadratic_mixture
-- name    : BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T15:04:43.047493+00:00
-- url     : https://prove2.me/theorems/bea02c80-f5c4-4a04-8431-0ba9ac10fe54
-- statement:
--   Let $d\in\mathbb N$ and $\lambda>0$. Prove that there exists a centered isotropic Gaussian probability measure $h=N(0,\lambda^{-1}I)$ on $\mathbb R^d$ such that, for every vector $S\in\mathbb R^d$ and every positive-semidefinite matrix $V\in\mathbb R^{d\times d}$, the function
--   $$
--   x\longmapsto
--   \exp\!\left(
--   \langle x,S\rangle-\frac12 x^\top Vx
--   \right)
--   $$
--   is integrable with respect to $h$ and
--   $$
--   \int_{\mathbb R^d}
--   \exp\!\left(
--   \langle x,S\rangle-\frac12 x^\top Vx
--   \right)\,dh(x)
--   =
--   \exp\!\left[
--   \frac12\left(
--   S^\top(\lambda I+V)^{-1}S
--   -\log\frac{\det(\lambda I+V)}{\lambda^d}
--   \right)
--   \right].
--   $$
--   This is the Gaussian completion-of-the-square identity used in the method of mixtures. The term $\lambda I$ comes from the Gaussian density, while $V$ is the unregularized quadratic variation.
--
--   Source: Tor Lattimore and Csaba Szepesvári, *Bandit Algorithms* (Cambridge University Press, 2020), Lemma 20.3 and equation (20.8), p. 259.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, p. 259, Lemma 20.3 and Eq. (20.8).

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open MeasureTheory ProbabilityTheory Matrix

theorem BanditAlgorithm.isotropic_gaussian_unregularized_quadratic_mixture
    {d : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ∃ h : Measure (Fin d → ℝ),
      IsProbabilityMeasure h ∧
      ∀ (S : Fin d → ℝ) (V : Matrix (Fin d) (Fin d) ℝ),
        V.PosSemidef →
        Integrable
            (fun x => Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x))) h ∧
          (∫ x, Real.exp
              (x ⬝ᵥ S - 1 / 2 * (x ⬝ᵥ V *ᵥ x)) ∂h) =
            Real.exp
              (1 / 2 *
                (S ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V)⁻¹ *ᵥ S -
                  Real.log
                    ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) + V).det / lam ^ d))) := by
  sorry
