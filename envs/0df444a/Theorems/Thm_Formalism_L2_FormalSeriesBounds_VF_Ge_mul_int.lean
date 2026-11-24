-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:58.544214+00:00
-- url     : https://prove2.me/theorems/a3adcd19-9adc-422c-bde8-1dbebb95a918
-- title:
--   Ge: mul int
-- statement:
--   The Ge construction uses the mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L63-L64

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

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge w b) : V.Ge w (a * b) := by sorry
