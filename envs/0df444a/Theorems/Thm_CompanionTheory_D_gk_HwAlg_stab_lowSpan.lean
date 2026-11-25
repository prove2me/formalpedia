-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_HwAlg_stab_lowSpan
-- name    : CompanionTheory.D.gk.HwAlg.stab_lowSpan
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:18:53.1538+00:00
-- url     : https://prove2.me/theorems/e15c5fe3-df4d-4a89-9a13-bb7e08ae28a3
-- title:
--   Hw Alg: stab low Span
-- statement:
--   The Hw Alg construction uses the stab low Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/EqSmulOfWeight.lean#L81-L89

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

theorem CompanionTheory.D.gk.HwAlg.stab_lowSpan (hF : GlRel F) (hw : IsHW F ν w) : Stab F (lowSpan F w) := by sorry
