-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_isFD
-- name    : Formalism.MainNotions.LeviCoordinates.rr_isFD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:47.098708+00:00
-- url     : https://prove2.me/theorems/192c45d1-22ec-4633-a72b-322895e446d9
-- title:
--   Levi Coordinates: rr is FD
-- statement:
--   The Levi Coordinates construction uses the rr is FD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L121-L127

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

theorem Formalism.MainNotions.LeviCoordinates.rr_isFD [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : IsFundamentalDomain Γ D μ := by sorry
