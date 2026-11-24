-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_lint
-- name    : Formalism.MainNotions.LeviCoordinates.rrkb_lint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:59.545897+00:00
-- url     : https://prove2.me/theorems/7ba2e005-ece7-4c74-ba23-c7dd813b292d
-- title:
--   Levi Coordinates: rrkb lint
-- statement:
--   The Levi Coordinates construction uses the rrkb lint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L38-L47

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

theorem Formalism.MainNotions.LeviCoordinates.rrkb_lint (h : rr_FD μ Γ D) {r : G → G} (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G)
    {F : G → ℝ≥0∞} (hF : Measurable F) : ∫⁻ x in D, F (r (x * g)) ∂μ = ∫⁻ x in D, F x ∂μ := by sorry
