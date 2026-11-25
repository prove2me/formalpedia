-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_map_maxGen
-- name    : CompanionTheory.RgExh.Hk.map_maxGen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:51:11.772938+00:00
-- url     : https://prove2.me/theorems/3b243756-f1f9-4973-afb5-05f0144a36ab
-- title:
--   Hk: map max Gen
-- statement:
--   The Hk construction uses the map max Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L22-L46

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}

theorem CompanionTheory.RgExh.Hk.map_maxGen {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (φ : M ≃ₗ[ℂ] M') (T : Module.End ℂ M) (T' : Module.End ℂ M') (hφ : ∀ x, φ (T x) = T' (φ x)) (μ : ℂ) :
    (T.maxGenEigenspace μ).map (φ : M →ₗ[ℂ] M') = T'.maxGenEigenspace μ := by sorry
