-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_inj_of
-- name    : Formalism.GM.DimensionMonotonicity.GlW.inj_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:23.883987+00:00
-- url     : https://prove2.me/theorems/d7b7eecc-2ce1-4e45-b290-8b4465d4ef65
-- title:
--   Gl W: inj of
-- statement:
--   The Gl W construction uses the inj of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L869-L907
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L869-L907

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.GM.DimensionMonotonicity.GlW.inj_of {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {W : Submodule K V} (hW : G.Stable W)
    (hWf : G.FinW W) (hvW : v ∈ W) (Φ : V →ₗ[K] V) (κ : Fin r → ℤ)
    (hΦE : ∀ x ∈ G.gS {v}, ∀ a b, a < b → Φ (G.E a b x) = G.E a b (Φ x))
    (hΦc : ∀ x ∈ G.gS {v}, ∀ ν, Φ (G.comp ν x) = G.comp (ν + κ) (Φ x)) (hΦv : Φ v ≠ 0) :
    ∀ x ∈ G.gS {v}, Φ x = 0 → x = 0 := by sorry
