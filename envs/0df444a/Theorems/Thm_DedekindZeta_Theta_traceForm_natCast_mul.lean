-- Prove2me | Theorems.Thm_DedekindZeta_Theta_traceForm_natCast_mul
-- name    : DedekindZeta.Theta.traceForm_natCast_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:13:08.773842+00:00
-- url     : https://prove2.me/theorems/bc13b1fa-9c07-4e6c-a992-dac16c416977
-- title:
--   Theta: trace Form nat Cast mul
-- statement:
--   `traceForm K η` scales by a natural number under the corresponding scaling of
--   its field argument: `T(η, n·a) = n·T(η, a)`. (`traceForm` factors through the
--   ring hom `mixedEmbedding` and the `ℝ`-linear `traceFormLin`, both of which
--   respect `n • ·`.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L647-L650
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L647-L650

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.traceForm_natCast_mul (η : mixedSpace K) (n : ℕ) (a : K) :
    traceForm K η ((n : K) * a) = n * traceForm K η a := by sorry
