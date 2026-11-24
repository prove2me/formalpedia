-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_conj_facts
-- name    : CompanionTheory.D.Upq.Sm.conj_facts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:57:45.356316+00:00
-- url     : https://prove2.me/theorems/09bc099b-e410-4bf5-a633-67555f85eb24
-- title:
--   Sm: conj facts
-- statement:
--   The Sm construction uses the conj facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/SmoothCyc.lean#L24-L42

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

theorem CompanionTheory.D.Upq.Sm.conj_facts {n : ℕ} {J Hm P : Mat n} (hP : IsUnit P) (hPJ : Pᴴ * J * P = Hm) :
    (∀ a : Mat n, aᴴ * Hm * a = Hm → ∃ b : Mat n, bᴴ * J * b = J ∧ P⁻¹ * b * P = a) ∧
      ∀ b : Mat n, bᴴ * J * b = J → (P⁻¹ * b * P)ᴴ * Hm * (P⁻¹ * b * P) = Hm := by sorry
