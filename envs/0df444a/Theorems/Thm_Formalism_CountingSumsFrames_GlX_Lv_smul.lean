-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_Lv_smul
-- name    : Formalism.CountingSumsFrames.GlX.Lv_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:23.71244+00:00
-- url     : https://prove2.me/theorems/ae457ba0-5588-4c69-983b-46f9a668295a
-- title:
--   Gl X: Lv smul
-- statement:
--   The Gl X construction uses the Lv smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L269-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L269-L272

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

theorem Formalism.CountingSumsFrames.GlX.Lv_smul (t : K) (v : V) (c : List (Fin r × Fin r) →₀ K) : Lv G (t • v) c = t • Lv G v c := by sorry
