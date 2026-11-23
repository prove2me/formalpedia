-- Prove2me | Theorems.Thm_DedekindZeta_Theta_summable_theta
-- name    : DedekindZeta.Theta.summable_theta
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:10:28.110547+00:00
-- url     : https://prove2.me/theorems/6038d6c9-b022-4554-bf29-e255e1bddbf7
-- title:
--   Theta: summable theta
-- statement:
--   **Convergence** (the standard treatment): for `t > 0` the theta series of a
--   nonzero fractional ideal converges absolutely.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L125-L242
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L125-L242

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.summable_theta {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    Summable fun x : (I : Submodule (𝓞 K) K) =>
      Real.exp (-Real.pi * t * ‖eEmb K (x : K)‖ ^ 2) := by sorry
