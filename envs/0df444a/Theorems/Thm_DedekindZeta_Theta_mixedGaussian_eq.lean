-- Prove2me | Theorems.Thm_DedekindZeta_Theta_mixedGaussian_eq
-- name    : DedekindZeta.Theta.mixedGaussian_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:54:43.7198+00:00
-- url     : https://prove2.me/theorems/7959055b-8ed0-4703-99be-dd98a40d02d8
-- title:
--   Theta: mixed Gaussian eq
-- statement:
--   **Bridge** `mixedGaussian = gaussV ∘ toMinkowski`: the Minkowski quadratic
--   form `∑_w mult w · normAtPlace w x²` equals `‖toMinkowski K x‖²` (the
--   `√2`-weighting puts the factor `2` on the complex places — the general-point
--   analog of `inner_eEmb`). Hence `(mixedGaussian K x : ℂ) = gaussV K (toMinkowski K x)`.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1348-L1402
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1348-L1402

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.mixedGaussian_eq (x : mixedEmbedding.mixedSpace K) :
    (mixedGaussian K x : ℂ) = gaussV K (toMinkowski K x) := by sorry
