-- Prove2me | Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_intOn
-- name    : Formalism.MainNotions.LeviCoordinates.rrc_intOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:04.960716+00:00
-- url     : https://prove2.me/theorems/52eaefca-4e4f-458e-ab51-4c0fba1ed485
-- title:
--   Levi Coordinates: rrc int On
-- statement:
--   The Levi Coordinates construction uses the rrc int On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrcTendstoVec.lean#L39-L41

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
  [BorelSpace G] [μ.IsHaarMeasure] [CompleteSpace H]

theorem Formalism.MainNotions.LeviCoordinates.rrc_intOn (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v u : H) : IntegrableOn (fun g => ⟪π g v, u⟫_ℂ) k μ := by sorry
