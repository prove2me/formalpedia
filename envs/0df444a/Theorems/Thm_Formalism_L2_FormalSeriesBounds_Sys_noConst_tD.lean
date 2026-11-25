-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_noConst_tD
-- name    : Formalism.L2.FormalSeriesBounds.Sys.noConst_tD
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:28:28.431059+00:00
-- url     : https://prove2.me/theorems/855158db-61f9-47f5-b03a-5fd8b252e312
-- title:
--   Sys: no Const t D
-- statement:
--   The Sys construction uses the no Const t D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L574-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L574-L575

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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.Sys.noConst_tD (W : τ → I → C) {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS W) (t c)) := by sorry
