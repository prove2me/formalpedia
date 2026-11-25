-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_X
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_X
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:27:28.869929+00:00
-- url     : https://prove2.me/theorems/778c8555-58d2-44a1-95c3-04ddef92a344
-- title:
--   Formal Series Bounds: subst lin S X
-- statement:
--   The Formal Series Bounds construction uses the subst lin S X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L211-L212

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.subst_linS_X [Finite σ] (M : τ → σ → C) (w : σ) :
    subst (linS M) (X w : MvPowerSeries σ C) = linS M w := by sorry
