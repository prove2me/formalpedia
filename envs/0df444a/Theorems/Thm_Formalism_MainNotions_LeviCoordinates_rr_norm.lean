-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_norm
-- name    : Formalism.MainNotions.LeviCoordinates.rr_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:21.791328+00:00
-- url     : https://prove2.me/theorems/ba6e146a-2f5e-4d84-8502-fb2f300a73bd
-- title:
--   Levi Coordinates: rr norm
-- statement:
--   The Levi Coordinates construction uses the rr norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L257-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L257-L266

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
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

theorem Formalism.MainNotions.LeviCoordinates.rr_norm [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) (g : G) (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by sorry
