-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_meas_pre
-- name    : Formalism.MainNotions.LeviCoordinates.rr_meas_pre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:16.955929+00:00
-- url     : https://prove2.me/theorems/a4796d19-f810-461a-b439-31ed5752e70d
-- title:
--   Levi Coordinates: rr meas pre
-- statement:
--   The Levi Coordinates construction uses the rr meas pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L158-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L158-L212

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

theorem Formalism.MainNotions.LeviCoordinates.rr_meas_pre [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G) {A : Set G} (hA : MeasurableSet A) :
    μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (A ∩ D) := by sorry
