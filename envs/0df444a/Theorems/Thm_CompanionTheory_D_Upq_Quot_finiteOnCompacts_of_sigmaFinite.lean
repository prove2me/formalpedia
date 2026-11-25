-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_finiteOnCompacts_of_sigmaFinite
-- name    : CompanionTheory.D.Upq.Quot.finiteOnCompacts_of_sigmaFinite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:30:31.114718+00:00
-- url     : https://prove2.me/theorems/028f30e1-77cc-47a0-b87f-cd066a08b109
-- title:
--   Quot: finite On Compacts of sigma Finite
-- statement:
--   The Quot construction uses the finite On Compacts of sigma Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L16-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L16-L33

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

theorem CompanionTheory.D.Upq.Quot.finiteOnCompacts_of_sigmaFinite (η : Measure H) [SigmaFinite η] [IsMulLeftInvariant η] :
    IsFiniteMeasureOnCompacts η := by sorry
