-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_tendsto_vec
-- name    : Formalism.MainNotions.LeviCoordinates.rrc_tendsto_vec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:15.133132+00:00
-- url     : https://prove2.me/theorems/31cc7b86-c8ad-43b3-aa0f-fb0d581b66fb
-- title:
--   Levi Coordinates: rrc tendsto vec
-- statement:
--   The Levi Coordinates construction uses the rrc tendsto vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L121-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L121-L141

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

theorem Formalism.MainNotions.LeviCoordinates.rrc_tendsto_vec (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) :
    Tendsto (fun h => π h w) (𝓝 1) (𝓝 w) := by sorry
