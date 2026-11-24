-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_ker_le
-- name    : Formalism.CountingSumsFrames.GlX.ker_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:45.043917+00:00
-- url     : https://prove2.me/theorems/32c7d3df-775d-41e0-90f1-b3b1cb42f540
-- title:
--   Gl X: ker le
-- statement:
--   The Gl X construction uses the ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L274-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L274-L308

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

theorem Formalism.CountingSumsFrames.GlX.ker_le {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h') := by sorry
