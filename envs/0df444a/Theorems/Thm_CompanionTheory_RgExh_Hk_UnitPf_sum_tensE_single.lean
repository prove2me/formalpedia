-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_sum_tensE_single
-- name    : CompanionTheory.RgExh.Hk.UnitPf.sum_tensE_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:52.152806+00:00
-- url     : https://prove2.me/theorems/40bdc027-b720-41e9-ae3a-a3df46ab878b
-- title:
--   Unit Pf: sum tens E single
-- statement:
--   The Unit Pf construction uses the sum tens E single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L61-L78

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedVariables false
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem CompanionTheory.RgExh.Hk.UnitPf.sum_tensE_single (v : X.V) (a : Fin (m + 1)) :
    ∑ c, tensE X a c (Pi.single c v) = om X (Pi.single a v) + ((m + 1 : ℕ) : ℂ) • (Pi.single a v : Fin (m + 1) → X.V) := by sorry
