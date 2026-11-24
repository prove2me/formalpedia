-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_iterate
-- name    : Formalism.L2.FormalSeriesBounds.Contr.noConst_iterate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:51.189335+00:00
-- url     : https://prove2.me/theorems/e3ac9991-3006-4047-a354-01a3b15eb5aa
-- title:
--   Contr: no Const iterate
-- statement:
--   The Contr construction uses the no Const iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L29-L35

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate

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
variable {k : Type*} [Field k] {Z B : Type*}
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H

theorem Formalism.L2.FormalSeriesBounds.Contr.noConst_iterate {t : B → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst (Ψ^[n] t) := by sorry
