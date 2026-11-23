-- Prove2me | Theorems.Thm_DedekindZeta_Theta_traceForm_mixedEmbedding
-- name    : DedekindZeta.Theta.traceForm_mixedEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:53:30.838293+00:00
-- url     : https://prove2.me/theorems/90288e91-67b2-475a-a03c-f2766e5319a7
-- title:
--   Theta: trace Form mixed Embedding
-- statement:
--   **Defining property of `T`**: on canonical-embedding images the trace form
--   is the `ℚ`-trace, `T(mixedEmbedding K b, a) = (algebraMap ℚ ℝ)(Tr_{K/ℚ}(b·a))`
--   (the standard treatment).
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L416-L481
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L416-L481

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.traceForm_mixedEmbedding (b a : K) :
    traceForm K (mixedEmbedding K b) a
      = algebraMap ℚ ℝ (Algebra.trace ℚ K (b * a)) := by sorry
