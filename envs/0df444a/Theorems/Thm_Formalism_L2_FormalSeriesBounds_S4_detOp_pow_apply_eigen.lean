-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_detOp_pow_apply_eigen
-- name    : Formalism.L2.FormalSeriesBounds.S4.detOp_pow_apply_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:42.78962+00:00
-- url     : https://prove2.me/theorems/f2fe76b3-56fd-4ea0-9d0f-f869c11ec72a
-- title:
--   S4: det Op pow apply eigen
-- statement:
--   The S4 construction uses the det Op pow apply eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L305-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L305-L313

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
variable {R : Type*} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.S4.detOp_pow_apply_eigen {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) (a : Matrix (Fin n) (Fin n) R) (g : F)
    (hD : ∀ ρ c, D ρ c g = a ρ c • g) (y : ℕ) : ((detOp D) ^ y) g = a.det ^ y • g := by sorry
