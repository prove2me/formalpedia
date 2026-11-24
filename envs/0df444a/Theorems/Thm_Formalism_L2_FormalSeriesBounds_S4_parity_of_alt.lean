-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_parity_of_alt
-- name    : Formalism.L2.FormalSeriesBounds.S4.parity_of_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:43.902807+00:00
-- url     : https://prove2.me/theorems/01a89451-652b-4ba5-b9dc-176e8b9821e4
-- title:
--   S4: parity of alt
-- statement:
--   The S4 construction uses the parity of alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L195-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L195-L200

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4

theorem Formalism.L2.FormalSeriesBounds.S4.parity_of_alt {d : ℕ} (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b)
    (a : ZMod d) (ha : big a) : ∀ k : ℕ, big (a + (k : ZMod d)) ↔ Even k := by sorry
