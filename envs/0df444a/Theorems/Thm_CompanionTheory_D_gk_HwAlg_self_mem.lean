-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_self_mem
-- name    : CompanionTheory.D.gk.HwAlg.self_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:53.941615+00:00
-- url     : https://prove2.me/theorems/16e86b87-e776-4ad4-a017-fdbe9625cd22
-- title:
--   Hw Alg: self mem
-- statement:
--   The Hw Alg construction uses the self mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L29-L30

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

theorem CompanionTheory.D.gk.HwAlg.self_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) : w ∈ lowSpan F w := by sorry
