-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_translate
-- name    : Formalism.MainNotions.LeviCoordinates.rrc_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:34.168358+00:00
-- url     : https://prove2.me/theorems/e82c0940-f4db-44fc-ac90-887eff17decd
-- title:
--   Levi Coordinates: rrc translate
-- statement:
--   The Levi Coordinates construction uses the rrc translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L66-L82

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
omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [CompleteSpace H]

theorem Formalism.MainNotions.LeviCoordinates.rrc_translate (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    {k : Set G} {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) (u : H) :
    ⟪π h w, u⟫_ℂ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := by sorry
