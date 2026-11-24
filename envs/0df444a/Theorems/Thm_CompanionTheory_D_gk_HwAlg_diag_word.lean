-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_diag_word
-- name    : CompanionTheory.D.gk.HwAlg.diag_word
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:26.066398+00:00
-- url     : https://prove2.me/theorems/9d7f5e7f-b184-43c4-b394-d405da0e7e20
-- title:
--   Hw Alg: diag word
-- statement:
--   The Hw Alg construction uses the diag word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L95-L108

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

theorem CompanionTheory.D.gk.HwAlg.diag_word (hF : GlRel F) (hw : IsHW F ν w) :
    ∀ (l : List (Fin n × Fin n)) (c : Fin n), F c c (word F l w) = wt ν l c • word F l w := by sorry
