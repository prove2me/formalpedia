-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_qlist_ne
-- name    : Formalism.CountingSumsFrames.GlX.qlist_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:42.512807+00:00
-- url     : https://prove2.me/theorems/dcc2841a-fde6-4d0e-bb54-e80a4269b040
-- title:
--   Gl X: qlist ne
-- statement:
--   The Gl X construction uses the qlist ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L53-L57

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.CountingSumsFrames.GlX.qlist_ne (S : Finset (Fin r → ℤ)) (c : ℤ) : ∀ x ∈ qlist S c, x ≠ c := by sorry
