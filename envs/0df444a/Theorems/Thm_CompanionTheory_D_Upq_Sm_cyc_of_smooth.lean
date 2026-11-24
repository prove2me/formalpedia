-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_cyc_of_smooth
-- name    : CompanionTheory.D.Upq.Sm.cyc_of_smooth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:10.252153+00:00
-- url     : https://prove2.me/theorems/aebf72b7-c31c-4718-9cd8-1040ab82c0a5
-- title:
--   Sm: cyc of smooth
-- statement:
--   The Sm construction uses the cyc of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L44-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L44-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI.UpqRep

theorem CompanionTheory.D.Upq.Sm.cyc_of_smooth (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) (w : H) (hσ : IsDSHpk k r ε lam σ) (hw0 : w ≠ 0)
    (hw : w ∈ smoothVecs (k := k) (r := r) σ) :
    ∀ x ∈ smoothVecs (k := k) (r := r) σ, ∀ Ws : List (List (Mat (2 * r + k + 1))),
    (∀ w' ∈ Ws, ∀ Y ∈ w', InLieHpk k r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat (2 * r + k + 1)),
      (∀ i, g i ∈ UH (Hpk k r)) ∧
      (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - ∑ i, c i • σ (g i) w)‖).sum < δ := by sorry
