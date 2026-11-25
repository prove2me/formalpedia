-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_map_comap_toM
-- name    : CompanionTheory.D.Upq.Quot.map_comap_toM
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:29:39.046537+00:00
-- url     : https://prove2.me/theorems/7f132e4d-98de-5ea5-aee3-90e924dbf83f
-- title:
--   Quot: map comap to M
-- statement:
--   The Quot construction uses the map comap to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L41-L44

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
open PI CompanionTheory.D.Upq.ModEx
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}

theorem CompanionTheory.D.Upq.Quot.map_comap_toM (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G) : (μ.comap (MG.toM (hG := hG))).map MG.toM = μ := by sorry
