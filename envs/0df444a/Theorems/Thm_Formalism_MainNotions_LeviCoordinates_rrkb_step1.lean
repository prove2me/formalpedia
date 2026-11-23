-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrkb_step1
-- name    : Formalism.MainNotions.LeviCoordinates.rrkb_step1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:15.415918+00:00
-- url     : https://prove2.me/theorems/697c17a5-12ba-46d1-81d9-9400309cc847
-- title:
--   Levi Coordinates: rrkb step1
-- statement:
--   The Levi Coordinates construction uses the rrkb step1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L119-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L119-L175

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

theorem Formalism.MainNotions.LeviCoordinates.rrkb_step1 (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ) {r : G → G} (hrm : Measurable r)
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ) (f : Lp ℂ 2 (μ.restrict D)) :
    ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D] fun x => ∫ g, φ g * (f : G → ℂ) (r (x * g)) ∂μ := by sorry
