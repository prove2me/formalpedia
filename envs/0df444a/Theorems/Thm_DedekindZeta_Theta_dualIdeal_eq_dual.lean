-- Prove2me | Theorems.Thm_DedekindZeta_Theta_dualIdeal_eq_dual
-- name    : DedekindZeta.Theta.dualIdeal_eq_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:11:19.422198+00:00
-- url     : https://prove2.me/theorems/992af66e-8e1b-4033-87b1-6cd17328b822
-- title:
--   Theta: dual Ideal eq dual
-- statement:
--   The `dualIdeal` is exactly Mathlib's trace-form dual fractional ideal
--   `FractionalIdeal.dual ℤ ℚ 𝔞` (the standard treatment: the trace dual of `𝔞` is
--   `(𝔞𝔡)⁻¹`, with `𝔡` the different).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L260-L266
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L260-L266

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.dualIdeal_eq_dual (𝔞 : Ideal (𝓞 K)) :
    FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = dualIdeal K 𝔞 := by sorry
