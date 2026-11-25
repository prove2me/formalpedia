-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_Pr_om_pow
-- name    : CompanionTheory.RgExh.Hk.UnitPf.Pr_om_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:12.81425+00:00
-- url     : https://prove2.me/theorems/9313cf6c-7c09-4f3b-823e-e5bd97497ae6
-- title:
--   Unit Pf: Pr om pow
-- statement:
--   The Unit Pf construction uses the Pr om pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/RightCasimirMemSubmodule.lean#L84-L88

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CommuteLeftRightCasimir
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_RightCasimirMemSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet GlRel)
open Formalism.QuantumDeterminants (capP)
open CompanionTheory.RgExh
variable {m : ℕ} {X : GMod (m + 1)} {χ : Fin (m + 1) → ℂ} {s : Fin (m + 1)}

theorem CompanionTheory.RgExh.Hk.UnitPf.Pr_om_pow (hS : ScalChar X χ) (k : ℕ) (f : Fin (m + 1) → X.V) :
    Pr X χ s ((om X ^ k) f) = (χ s - cn (m + 1)) ^ k • Pr X χ s f := by sorry
