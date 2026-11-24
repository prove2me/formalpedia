-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_pow
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:50.279083+00:00
-- url     : https://prove2.me/theorems/66dffff6-820e-4986-a53c-3ca2939f14c1
-- title:
--   Ge: pow
-- statement:
--   The Ge construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L56-L61

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

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.pow {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by sorry
