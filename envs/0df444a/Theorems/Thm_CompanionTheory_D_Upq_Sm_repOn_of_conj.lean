-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_repOn_of_conj
-- name    : CompanionTheory.D.Upq.Sm.repOn_of_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:57:05.557366+00:00
-- url     : https://prove2.me/theorems/b0c1c268-4f96-4ea0-bd3e-99937233bb26
-- title:
--   Sm: rep On of conj
-- statement:
--   The Sm construction uses the rep On of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/PhMeas.lean#L22-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SmoothCyclicVectors/PhMeas.lean#L22-L49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
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
open PI.PhMeasCore
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem CompanionTheory.D.Upq.Sm.repOn_of_conj {J Hm P : Mat n} {σ : Mat n → (H →L[ℂ] H)} (hP : IsUnit P)
    (hPJ : Pᴴ * J * P = Hm) (h1 : σ (P⁻¹ * 1 * P) = 1)
    (hm : ∀ a, aᴴ * J * a = J → ∀ b, bᴴ * J * b = J →
      σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) :
    RepOn {g | gᴴ * Hm * g = Hm} σ := by sorry
