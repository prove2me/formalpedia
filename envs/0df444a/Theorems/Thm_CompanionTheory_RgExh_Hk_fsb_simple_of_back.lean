-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_fsb_simple_of_back
-- name    : CompanionTheory.RgExh.Hk.fsb_simple_of_back
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:08:51.810413+00:00
-- url     : https://prove2.me/theorems/44cddbd0-c60b-518e-88c1-58ad33c28b09
-- title:
--   Hk: fsb simple of back
-- statement:
--   The Hk construction uses the fsb simple of back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L245-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/SimpleBackwardTransfer/FwdSimpleOfb.lean#L245-L277

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatementStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_SimpleBackwardTransfer_FwdSimpleOfb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
variable {n : ℕ}

theorem CompanionTheory.RgExh.Hk.fsb_simple_of_back (hD : DualFacts) (X S : GMod n) (χ' : Fin n → ℂ) (s : Fin n) (z : ℂ) (hz : χ' s = z)
    (hX : IsSimple X) (hS : HasChar S χ') (h1 : ∀ t, t ≠ s → χ' t ≠ z) (h2 : ∀ r, χ' r ≠ z - 1)
    (hB : ∀ a b, ∀ x ∈ backSub S z, (tensD S).E a b x ∈ backSub S z)
    (hI : Iso (back S z hB) X) : IsSimple S := by sorry
