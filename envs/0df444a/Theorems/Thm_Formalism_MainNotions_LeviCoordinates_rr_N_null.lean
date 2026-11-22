-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_null
-- name    : Formalism.MainNotions.LeviCoordinates.rr_N_null
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:46.613247+00:00
-- url     : https://prove2.me/theorems/fc79406d-893e-489f-9ec9-4912e8d88d24
-- title:
--   Levi Coordinates: rr N null
-- statement:
--   The Levi Coordinates construction uses the rr N null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L42-L54

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

theorem Formalism.MainNotions.LeviCoordinates.rr_N_null [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : μ (rr_N Γ D) = 0 := by sorry
