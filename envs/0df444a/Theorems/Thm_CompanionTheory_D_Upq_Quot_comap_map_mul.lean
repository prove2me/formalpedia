-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_comap_map_mul
-- name    : CompanionTheory.D.Upq.Quot.comap_map_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:22.035599+00:00
-- url     : https://prove2.me/theorems/37c75224-35d8-431c-822e-8650646155fa
-- title:
--   Quot: comap map mul
-- statement:
--   The Quot construction uses the comap map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L46-L53

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

theorem CompanionTheory.D.Upq.Quot.comap_map_mul (hG : IsMatGroup G) {μ : Measure (MtM m)} (h0 : ∀ᵐ x ∂μ, Matrix.of x ∈ G)
    (g : MG G hG) (hl : μ.map (lmulQ g.mat) = μ) :
    (μ.comap (MG.toM (hG := hG))).map (g * ·) = μ.comap MG.toM := by sorry
