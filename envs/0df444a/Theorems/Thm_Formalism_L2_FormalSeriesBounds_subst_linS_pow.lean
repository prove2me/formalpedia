-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_pow
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:02:58.448069+00:00
-- url     : https://prove2.me/theorems/42cf70f4-b935-4dec-b07e-b5f0284cd8bc
-- title:
--   Formal Series Bounds: subst lin S pow
-- statement:
--   The Formal Series Bounds construction uses the subst lin S pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L205-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L205-L206

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.subst_linS_pow [Finite σ] (M : τ → σ → C) (F : MvPowerSeries σ C) (n : ℕ) :
    subst (linS M) (F ^ n) = subst (linS M) F ^ n := by sorry
