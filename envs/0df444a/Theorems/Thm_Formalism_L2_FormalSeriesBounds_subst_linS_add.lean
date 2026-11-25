-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_add
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:25.172164+00:00
-- url     : https://prove2.me/theorems/47c2227a-a757-4b0a-a4ca-6358ccf751cb
-- title:
--   Formal Series Bounds: subst lin S add
-- statement:
--   The Formal Series Bounds construction uses the subst lin S add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L196-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L196-L197

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_add [Finite σ] (M : τ → σ → C) (F G : MvPowerSeries σ C) :
    subst (linS M) (F + G) = subst (linS M) F + subst (linS M) G := by sorry
