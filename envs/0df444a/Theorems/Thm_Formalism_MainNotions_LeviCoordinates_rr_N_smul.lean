-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_smul
-- name    : Formalism.MainNotions.LeviCoordinates.rr_N_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:50.35508+00:00
-- url     : https://prove2.me/theorems/43ff791c-7617-4e44-86b8-5c935e5951cb
-- title:
--   Levi Coordinates: rr N smul
-- statement:
--   The Levi Coordinates construction uses the rr N smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L70-L76

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
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
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

theorem Formalism.MainNotions.LeviCoordinates.rr_N_smul {y c : G} (hc : c ∈ Γ) (hy : y ∉ rr_N Γ D) : c * y ∉ rr_N Γ D := by sorry
