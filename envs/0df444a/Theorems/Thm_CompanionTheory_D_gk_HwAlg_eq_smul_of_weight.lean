-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_eq_smul_of_weight
-- name    : CompanionTheory.D.gk.HwAlg.eq_smul_of_weight
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:40.293772+00:00
-- url     : https://prove2.me/theorems/abbd6340-ed58-5c3c-b4b1-58ce6b4dfe4d
-- title:
--   Hw Alg: eq smul of weight
-- statement:
--   The Hw Alg construction uses the eq smul of weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L138-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L138-L176

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

theorem CompanionTheory.D.gk.HwAlg.eq_smul_of_weight (hF : GlRel F) (hw : IsHW F ν w) {x : U} (hx : x ∈ lowSpan F w)
    (hxν : ∀ c, F c c x = ν c • x) : ∃ t : ℂ, x = t • w := by sorry
