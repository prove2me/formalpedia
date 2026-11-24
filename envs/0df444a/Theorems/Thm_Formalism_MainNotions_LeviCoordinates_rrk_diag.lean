-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrk_diag
-- name    : Formalism.MainNotions.LeviCoordinates.rrk_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:11.721793+00:00
-- url     : https://prove2.me/theorems/b8f950ae-3faa-4aea-83d5-0bc56d97c75c
-- title:
--   Levi Coordinates: rrk diag
-- statement:
--   The Levi Coordinates construction uses the rrk diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkDiag.lean#L10-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrkDiag.lean#L10-L59

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkDiag
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
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

theorem Formalism.MainNotions.LeviCoordinates.rrk_diag {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SeparableSpace (Lp ℂ 2 ν)]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hT : IsStarProjection T) {N : ℕ}
    (F : OrthonormalBasis (Fin N) ℂ (LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)))
    (κ : Y → Lp ℂ 2 ν) (hκ : ∀ f : Lp ℂ 2 ν, ∀ᵐ x ∂ν, (T f : Y → ℂ) x = ⟪κ x, f⟫_ℂ) :
    ∀ᵐ x ∂ν, ‖κ x‖ ^ 2 = ∑ w, ‖(((F w : LinearMap.range (T : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) : Lp ℂ 2 ν) : Y → ℂ) x‖ ^ 2 := by sorry
