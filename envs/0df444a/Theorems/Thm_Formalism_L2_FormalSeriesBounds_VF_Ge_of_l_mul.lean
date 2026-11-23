-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.of_l_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:50.430873+00:00
-- url     : https://prove2.me/theorems/20ad8a5c-5433-4439-a940-229a790b9769
-- title:
--   Ge: of l mul
-- statement:
--   The Ge construction uses the of l mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L79-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L79-L89

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

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.of_l_mul {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) * a)) : V.Ge (w - 1) a := by sorry
