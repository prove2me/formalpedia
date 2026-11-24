-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_pj_dens_meas
-- name    : Formalism.MainNotions.LeviCoordinates.pj_dens_meas
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:53.771046+00:00
-- url     : https://prove2.me/theorems/8022e678-94f9-4ed8-9a7a-4249cf18a804
-- title:
--   Levi Coordinates: pj dens meas
-- statement:
--   The Levi Coordinates construction uses the pj dens meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/PjDensUpper.lean#L33-L34

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

theorem Formalism.MainNotions.LeviCoordinates.pj_dens_meas (hm : ∀ x y : Hs, AEStronglyMeasurable (fun g => ⟪y, σ g x⟫_ℂ) μ) (x y : Hs) :
    AEStronglyMeasurable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ := by sorry
