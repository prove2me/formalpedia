-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_cont_of_meas
-- name    : Formalism.MainNotions.LeviCoordinates.rr_cont_of_meas
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:35.194995+00:00
-- url     : https://prove2.me/theorems/46b2dd4e-e551-4fdf-8f20-d1e372318b68
-- title:
--   Levi Coordinates: rr cont of meas
-- statement:
--   The Levi Coordinates construction uses the rr cont of meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L182-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L182-L212

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
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
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}

theorem Formalism.MainNotions.LeviCoordinates.rr_cont_of_meas [TopologicalSpace.SeparableSpace H] (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1)
    (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) (x : H) :
    Continuous fun g => π g x := by sorry
