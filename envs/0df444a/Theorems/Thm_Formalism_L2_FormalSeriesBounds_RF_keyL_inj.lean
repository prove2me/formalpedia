-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_keyL_inj
-- name    : Formalism.L2.FormalSeriesBounds.RF.keyL_inj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:01.607806+00:00
-- url     : https://prove2.me/theorems/173c344a-07a8-4c8d-a444-bae4ed5107d8
-- title:
--   RF: key L inj
-- statement:
--   The RF construction uses the key L inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowInvariant.lean#L18-L23

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.keyL_inj : Function.Injective (keyL (T := T) (r := r) (n := n)) := by sorry
