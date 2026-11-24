-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_gen_mem
-- name    : CompanionTheory.D.gk.HwAlg.gen_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:49.310809+00:00
-- url     : https://prove2.me/theorems/ea56057c-f1e4-45aa-828b-cf173e002f16
-- title:
--   Hw Alg: gen mem
-- statement:
--   The Hw Alg construction uses the gen mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L57-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L57-L79

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.FourierDecayAlt.Qr
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.HwAlg
variable {U : Type} [AddCommGroup U] [Module ℂ U] {n : ℕ}
variable {F : Fin n → Fin n → Module.End ℂ U} {ν : Fin n → ℂ} {w : U}

theorem CompanionTheory.D.gk.HwAlg.gen_mem (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)), Lower l → ∀ i j, F i j (word F l w) ∈ lowSpan F w := by sorry
