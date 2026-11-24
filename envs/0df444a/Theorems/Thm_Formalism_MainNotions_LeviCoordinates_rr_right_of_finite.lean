-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_right_of_finite
-- name    : Formalism.MainNotions.LeviCoordinates.rr_right_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:17.133887+00:00
-- url     : https://prove2.me/theorems/4c397a0c-666a-4241-ac3f-543d5f54087f
-- title:
--   Levi Coordinates: rr right of finite
-- statement:
--   The Levi Coordinates construction uses the rr right of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrRightOfFinite.lean#L15-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrRightOfFinite.lean#L15-L49

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrRightOfFinite
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
open scoped ENNReal Pointwise
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

theorem Formalism.MainNotions.LeviCoordinates.rr_right_of_finite [SigmaFinite μ] [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (hfin : μ D ≠ ⊤) :
    μ.IsMulRightInvariant := by sorry
