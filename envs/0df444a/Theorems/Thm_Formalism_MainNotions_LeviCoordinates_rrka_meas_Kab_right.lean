-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_meas_Kab_right
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_meas_Kab_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:01.433172+00:00
-- url     : https://prove2.me/theorems/2acd26ee-1d23-425c-8ece-dbfdae40a20b
-- title:
--   Levi Coordinates: rrka meas Kab right
-- statement:
--   The Levi Coordinates construction uses the rrka meas Kab right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L53-L54

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem Formalism.MainNotions.LeviCoordinates.rrka_meas_Kab_right (hφm : Measurable φ) (x : G) : Measurable fun y => rrk_Kab Γ φ x y := by sorry
