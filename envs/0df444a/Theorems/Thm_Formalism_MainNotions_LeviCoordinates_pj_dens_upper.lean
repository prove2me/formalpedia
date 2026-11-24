-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_upper
-- name    : Formalism.MainNotions.LeviCoordinates.pj_dens_upper
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:58.541819+00:00
-- url     : https://prove2.me/theorems/b75563c7-0ce0-4fb3-b88a-51c527585205
-- title:
--   Levi Coordinates: pj dens upper
-- statement:
--   The Levi Coordinates construction uses the pj dens upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L36-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L36-L64

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_PjDensUpper
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
open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs]
  [InnerProductSpace ℂ Hs] (σ : G → (Hs →L[ℂ] Hs))

theorem Formalism.MainNotions.LeviCoordinates.pj_dens_upper (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ)
    (V : Submodule ℂ Hs) (hV : Dense (V : Set Hs)) (d : ℝ)
    (h : ∀ x ∈ V, ∀ y ∈ V, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) (hd : 0 < d) (x y : Hs) :
    Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧ ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 / d := by sorry
