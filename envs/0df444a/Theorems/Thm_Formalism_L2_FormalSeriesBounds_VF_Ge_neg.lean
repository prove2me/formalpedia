-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:21.589346+00:00
-- url     : https://prove2.me/theorems/ba0e5527-1633-4e00-954c-1356539ca22f
-- title:
--   Ge: neg
-- statement:
--   The Ge construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L34-L37

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C]
open Formalism.L2.FormalSeriesBounds.VF
variable (V : VF C)
variable {V}

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.neg {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by sorry
