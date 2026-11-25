-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_right_casimir_add_eta_psi
-- name    : CompanionTheory.RgExh.Hk.UnitPf.right_casimir_add_eta_psi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:54:39.24923+00:00
-- url     : https://prove2.me/theorems/8b8b6d1e-548d-45aa-898b-c24419ea0671
-- title:
--   Unit Pf: right casimir add eta psi
-- statement:
--   The Unit Pf construction uses the right casimir add eta psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L86-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CommuteLeftRightCasimir.lean#L86-L93

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

theorem CompanionTheory.RgExh.Hk.UnitPf.right_casimir_add_eta_psi (H : Fin (m + 1) → Fin (m + 1) → X.V) (a d : Fin (m + 1)) :
    (y2 X H + eta X (psi X H)) a d = -∑ c, X.E a c (H c d) := by sorry
