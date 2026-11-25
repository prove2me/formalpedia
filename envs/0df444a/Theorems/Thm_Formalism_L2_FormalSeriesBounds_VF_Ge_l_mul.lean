-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
-- name    : Formalism.L2.FormalSeriesBounds.VF.Ge.l_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:34.825289+00:00
-- url     : https://prove2.me/theorems/dd9bea3e-fb6c-4049-b04d-32a99ff65c7f
-- title:
--   Ge: l mul
-- statement:
--   The Ge construction uses the l mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeNatCast.lean#L91-L94

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

theorem Formalism.L2.FormalSeriesBounds.VF.Ge.l_mul {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (1 + w) ((V.l : C) * a) := by sorry
