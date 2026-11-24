-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_fix_fixPt
-- name    : Formalism.L2.FormalSeriesBounds.Contr.fix_fixPt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:42.481538+00:00
-- url     : https://prove2.me/theorems/8e7b54e9-e902-42bb-a633-ed3ee299d59f
-- title:
--   Contr: fix fix Pt
-- statement:
--   The Contr construction uses the fix fix Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffIterateZero.lean#L74-L80

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
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H

theorem Formalism.L2.FormalSeriesBounds.Contr.fix_fixPt : Ψ H.fixPt = H.fixPt := by sorry
