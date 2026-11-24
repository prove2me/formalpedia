-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_noConst_iff
-- name    : Formalism.L2.FormalSeriesBounds.noConst_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:45.1098+00:00
-- url     : https://prove2.me/theorems/4a5d3b95-c6e4-4aef-8fda-201fc4eb5e27
-- title:
--   Formal Series Bounds: no Const iff
-- statement:
--   The Formal Series Bounds construction uses the no Const iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L93-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L93-L107

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
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

theorem Formalism.L2.FormalSeriesBounds.noConst_iff (t : B → MvPowerSeries Z k) :
    NoConst t ↔ ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := by sorry
