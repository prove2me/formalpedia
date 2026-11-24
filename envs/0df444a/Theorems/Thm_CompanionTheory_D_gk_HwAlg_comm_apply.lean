-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_comm_apply
-- name    : CompanionTheory.D.gk.HwAlg.comm_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:49:02.325376+00:00
-- url     : https://prove2.me/theorems/8a4fac22-08f6-499a-95db-46fffba83808
-- title:
--   Hw Alg: comm apply
-- statement:
--   The Hw Alg construction uses the comm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L48-L53

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

theorem CompanionTheory.D.gk.HwAlg.comm_apply {F : Fin n → Fin n → Module.End ℂ U} (hF : GlRel F) (i j a b : Fin n) (u : U) :
    F i j (F a b u) = F a b (F i j u) +
      ((if j = a then F i b u else 0) - (if b = i then F a j u else 0)) := by sorry
