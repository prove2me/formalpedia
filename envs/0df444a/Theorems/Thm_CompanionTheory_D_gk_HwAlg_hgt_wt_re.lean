-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_hgt_wt_re
-- name    : CompanionTheory.D.gk.HwAlg.hgt_wt_re
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:33.867808+00:00
-- url     : https://prove2.me/theorems/88a7b581-d924-447c-9f77-0a8c39fb88f1
-- title:
--   Hw Alg: hgt wt re
-- statement:
--   The Hw Alg construction uses the hgt wt re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L112-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L112-L130

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

theorem CompanionTheory.D.gk.HwAlg.hgt_wt_re (ν : Fin n → ℂ) :
    ∀ l : List (Fin n × Fin n), Lower l → (hgt (wt ν l)).re ≤ (hgt ν).re - l.length := by sorry
