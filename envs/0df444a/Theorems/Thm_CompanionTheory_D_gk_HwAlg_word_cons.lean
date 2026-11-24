-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
-- name    : CompanionTheory.D.gk.HwAlg.word_cons
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:48:46.535476+00:00
-- url     : https://prove2.me/theorems/49810289-10f6-4041-8c7b-4f7f8c3926af
-- title:
--   Hw Alg: word cons
-- statement:
--   The Hw Alg construction uses the word cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L18-L20

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

theorem CompanionTheory.D.gk.HwAlg.word_cons (F : Fin n → Fin n → Module.End ℂ U) (p : Fin n × Fin n) (l : List (Fin n × Fin n)) :
    word F (p :: l) = F p.1 p.2 * word F l := by sorry
