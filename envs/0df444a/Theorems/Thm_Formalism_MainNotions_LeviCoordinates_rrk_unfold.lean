-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrk_unfold
-- name    : Formalism.MainNotions.LeviCoordinates.rrk_unfold
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:21.559381+00:00
-- url     : https://prove2.me/theorems/4408231d-95e5-4fd7-b175-2c68775808d8
-- title:
--   Levi Coordinates: rrk unfold
-- statement:
--   The Levi Coordinates construction uses the rrk unfold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L177-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkbLeOneAddSq.lean#L177-L187

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

theorem Formalism.MainNotions.LeviCoordinates.rrk_unfold (h : rr_FD μ Γ D) {φ : G → ℂ} (hφm : Measurable φ)
    {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))} (hR : rr_IsReg μ Γ D R)
    (T : Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D)) (hφ : Integrable φ μ)
    (hT : ∀ u v : Lp ℂ 2 (μ.restrict D), ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, R g v⟫_ℂ ∂μ)
    (hK : ∀ᵐ x ∂μ.restrict D, ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) (f : Lp ℂ 2 (μ.restrict D)) :
    ∀ᵐ x ∂μ.restrict D, ((T f : Lp ℂ 2 (μ.restrict D)) : G → ℂ) x =
      ∫ y in D, rrk_K Γ φ x y * (f : G → ℂ) y ∂μ := by sorry
