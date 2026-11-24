-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_step2
-- name    : Formalism.MainNotions.LeviCoordinates.rrkb_step2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:12.710146+00:00
-- url     : https://prove2.me/theorems/bf513626-60c1-446f-9f0e-1ee05dbd336a
-- title:
--   Levi Coordinates: rrkb step2
-- statement:
--   The Levi Coordinates construction uses the rrkb step2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L80-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L80-L117

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

theorem Formalism.MainNotions.LeviCoordinates.rrkb_step2 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (f : Lp ℂ 2 (μ.restrict D)) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ = ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by sorry
