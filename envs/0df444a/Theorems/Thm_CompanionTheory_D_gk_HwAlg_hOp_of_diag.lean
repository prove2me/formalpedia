-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_hOp_of_diag
-- name    : CompanionTheory.D.gk.HwAlg.hOp_of_diag
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:02.483923+00:00
-- url     : https://prove2.me/theorems/05e17bdb-e926-462e-b56d-14c3a2d00e95
-- title:
--   Hw Alg: h Op of diag
-- statement:
--   The Hw Alg construction uses the h Op of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L135-L136

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

theorem CompanionTheory.D.gk.HwAlg.hOp_of_diag {x : U} {μ : Fin n → ℂ} (hx : ∀ c, F c c x = μ c • x) : hOp F x = hgt μ • x := by sorry
