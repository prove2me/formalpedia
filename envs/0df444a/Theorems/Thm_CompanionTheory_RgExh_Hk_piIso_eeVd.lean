-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_piIso_eeVd
-- name    : CompanionTheory.RgExh.Hk.piIso_eeVd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:57.44598+00:00
-- url     : https://prove2.me/theorems/17a8f80f-e47a-59ff-b813-68665fce1581
-- title:
--   Hk: pi Iso ee Vd
-- statement:
--   The Hk construction uses the pi Iso ee Vd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean#L65-L68

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

theorem CompanionTheory.RgExh.Hk.piIso_eeVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (f : Fin n → X.V) : piIso e (eeVd X.E f) = eeVd X'.E (piIso e f) := by sorry
