-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_FD_right
-- name    : Formalism.MainNotions.LeviCoordinates.rr_FD_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:39.589435+00:00
-- url     : https://prove2.me/theorems/aa80a24e-25da-46c0-9593-23989000b4a9
-- title:
--   Levi Coordinates: rr FD right
-- statement:
--   The Levi Coordinates construction uses the rr FD right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrExistsMeasRep.lean#L101-L113

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

theorem Formalism.MainNotions.LeviCoordinates.rr_FD_right [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (g : G) : rr_FD μ Γ ((fun x => x * g) ⁻¹' D) := by sorry
