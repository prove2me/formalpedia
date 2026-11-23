-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_frobSum_const
-- name    : Formalism.L2.FormalSeriesBounds.S4.frobSum_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:04.28585+00:00
-- url     : https://prove2.me/theorems/dafe899c-ae8d-4f40-9b26-127b264fbb29
-- title:
--   S4: frob Sum const
-- statement:
--   The S4 construction uses the frob Sum const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L250-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L250-L267

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

theorem Formalism.L2.FormalSeriesBounds.S4.frobSum_const {d : ℕ} {l : ℕ} (hl : 1 < l) (P : ℕ) (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) : frobSum l p a = (P : ℝ) / ((l : ℝ) - 1) := by sorry
