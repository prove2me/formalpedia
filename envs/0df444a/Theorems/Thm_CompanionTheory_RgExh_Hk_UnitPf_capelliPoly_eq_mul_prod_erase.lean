-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_Hk_UnitPf_capelliPoly_eq_mul_prod_erase
-- name    : CompanionTheory.RgExh.Hk.UnitPf.capelliPoly_eq_mul_prod_erase
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:32:28.657802+00:00
-- url     : https://prove2.me/theorems/1d73f9bb-ee99-5fcb-9e02-11006d6f1410
-- title:
--   Unit Pf: capelli Poly eq mul prod erase
-- statement:
--   The Unit Pf construction uses the capelli Poly eq mul prod erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CompLeftSmulOne.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CompLeftSmulOne.lean#L33-L35

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
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
open CompanionTheory CompanionTheory.RgExh CompanionTheory.RgExh.Hk CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh
variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))
variable {X χ s}

theorem CompanionTheory.RgExh.Hk.UnitPf.capelliPoly_eq_mul_prod_erase (u : ℂ) :
    capP χ u = (u + χ s) * ∏ t ∈ univ.erase s, (u + χ t) := by sorry
