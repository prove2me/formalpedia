-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_r_fix
-- name    : Formalism.MainNotions.LeviCoordinates.rrkb_r_fix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:04.807433+00:00
-- url     : https://prove2.me/theorems/5e591432-35d4-43f0-bbab-dda77ca377b0
-- title:
--   Levi Coordinates: rrkb r fix
-- statement:
--   The Levi Coordinates construction uses the rrkb r fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L49-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L49-L78

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkbLeOneAddSq
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
  {μ : Measure G} [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {Γ : Subgroup G} [Countable Γ] {D : Set G}

theorem Formalism.MainNotions.LeviCoordinates.rrkb_r_fix (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) :
    ∀ᵐ y ∂μ.restrict D, ∀ γ : Γ, r ((γ : G) * y) = y := by sorry
