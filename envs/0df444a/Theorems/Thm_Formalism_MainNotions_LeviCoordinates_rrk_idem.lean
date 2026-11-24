-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrk_idem
-- name    : Formalism.MainNotions.LeviCoordinates.rrk_idem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:01.576431+00:00
-- url     : https://prove2.me/theorems/2d25ca6e-e138-466b-a5a7-a8e281a76966
-- title:
--   Levi Coordinates: rrk idem
-- statement:
--   The Levi Coordinates construction uses the rrk idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L74-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L74-L157

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight
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
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}

theorem Formalism.MainNotions.LeviCoordinates.rrk_idem [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ)
    (hsa : ∀ z, φ z⁻¹ = star (φ z)) (hid : ∀ z, ∫ g, φ g * φ (g⁻¹ * z) ∂μ = φ z) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    Summable (fun γ : Γ => φ (x⁻¹ * (γ : G) * x)) ∧
      rrk_K Γ φ x x = ((∫ y in D, ‖rrk_K Γ φ x y‖ ^ 2 ∂μ : ℝ) : ℂ) ∧
      MemLp (fun y => rrk_K Γ φ x y) 2 (μ.restrict D) := by sorry
