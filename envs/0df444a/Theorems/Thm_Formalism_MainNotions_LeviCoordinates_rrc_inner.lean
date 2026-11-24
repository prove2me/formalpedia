-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_inner
-- name    : Formalism.MainNotions.LeviCoordinates.rrc_inner
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:44.121884+00:00
-- url     : https://prove2.me/theorems/79d38e31-470d-4b52-ac8c-e06be867ca15
-- title:
--   Levi Coordinates: rrc inner
-- statement:
--   The Levi Coordinates construction uses the rrc inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L20-L21

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
omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [CompleteSpace H]

theorem Formalism.MainNotions.LeviCoordinates.rrc_inner (hn : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) (a b : H) : ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ := by sorry
