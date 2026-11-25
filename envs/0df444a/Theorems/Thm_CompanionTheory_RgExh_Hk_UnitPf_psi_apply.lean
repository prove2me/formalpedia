-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_psi_apply
-- name    : CompanionTheory.RgExh.Hk.UnitPf.psi_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:03.904822+00:00
-- url     : https://prove2.me/theorems/fd019460-b956-495a-892a-d4caa0d020c9
-- title:
--   Unit Pf: psi apply
-- statement:
--   The Unit Pf construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L52-L52

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

theorem CompanionTheory.RgExh.Hk.UnitPf.psi_apply (H : Fin (m + 1) → Fin (m + 1) → X.V) : psi X H = ∑ c, H c c := by sorry
