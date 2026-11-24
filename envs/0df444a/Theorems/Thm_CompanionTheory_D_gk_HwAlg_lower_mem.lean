-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_lower_mem
-- name    : CompanionTheory.D.gk.HwAlg.lower_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:14.285161+00:00
-- url     : https://prove2.me/theorems/02a14c14-5d61-4945-b969-8fdc7e5a8094
-- title:
--   Hw Alg: lower mem
-- statement:
--   The Hw Alg construction uses the lower mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L32-L46

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

theorem CompanionTheory.D.gk.HwAlg.lower_mem (F : Fin n → Fin n → Module.End ℂ U) (w : U) {a b : Fin n} (hab : b < a) {x : U}
    (hx : x ∈ lowSpan F w) : F a b x ∈ lowSpan F w := by sorry
