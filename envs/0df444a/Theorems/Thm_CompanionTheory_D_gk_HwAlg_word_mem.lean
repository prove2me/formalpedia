-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_mem
-- name    : CompanionTheory.D.gk.HwAlg.word_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:49:39.144844+00:00
-- url     : https://prove2.me/theorems/a0ba3a14-e812-49a3-bfb2-49d06d10a5e9
-- title:
--   Hw Alg: word mem
-- statement:
--   The Hw Alg construction uses the word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L25-L27

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

theorem CompanionTheory.D.gk.HwAlg.word_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {l : List (Fin n × Fin n)} (hl : Lower l) :
    word F l w ∈ lowSpan F w := by sorry
