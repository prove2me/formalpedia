-- Prove2me | Theorems.Thm_DedekindZeta_Theta_toMinkowski_inner
-- name    : DedekindZeta.Theta.toMinkowski_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:17:05.44682+00:00
-- url     : https://prove2.me/theorems/8ba9ad11-9a53-45bb-93e2-d69bf8f42a58
-- title:
--   Theta: to Minkowski inner
-- statement:
--   **Bilinear Minkowski inner product through `toMinkowski`.** The Euclidean
--   inner product of `toMinkowski K p` and `toMinkowski K q` expands per place as
--   `∑_real p₁ q₁ + 2 ∑_cplx Re(conj p₂ q₂)` (the `√2`-weighting on `scaleMixed`
--   puts the factor `2` on the complex places). The single-argument case is the
--   quadratic form used in `mixedGaussian_eq`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1473-L1510
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1473-L1510

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.toMinkowski_inner (p q : mixedEmbedding.mixedSpace K) :
    (inner ℝ (toMinkowski K p) (toMinkowski K q) : ℝ) =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (p.1 w) * (q.1 w)) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((p.2 w) * (starRingEnd ℂ) (q.2 w)).re := by sorry
