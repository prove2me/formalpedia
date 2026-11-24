-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_lint
-- name    : Formalism.MainNotions.LeviCoordinates.rrka_lint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:08.045802+00:00
-- url     : https://prove2.me/theorems/e2586703-fcf6-4a0a-ba43-5a44950b40a0
-- title:
--   Levi Coordinates: rrka lint
-- statement:
--   The Levi Coordinates construction uses the rrka lint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L56-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkaMeasKabRight.lean#L56-L69

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

theorem Formalism.MainNotions.LeviCoordinates.rrka_lint [μ.IsMulLeftInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ) (hsa : ∀ z, φ z⁻¹ = star (φ z)) (x : G) :
    ∫⁻ y, ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by sorry
