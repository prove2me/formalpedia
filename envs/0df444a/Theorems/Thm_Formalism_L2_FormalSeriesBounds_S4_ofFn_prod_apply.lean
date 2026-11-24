-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ofFn_prod_apply
-- name    : Formalism.L2.FormalSeriesBounds.S4.ofFn_prod_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:36.894955+00:00
-- url     : https://prove2.me/theorems/7f22ede9-d990-4787-8d6a-ece87bd2e0b8
-- title:
--   S4: of Fn prod apply
-- statement:
--   The S4 construction uses the of Fn prod apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L279-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L279-L293

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

theorem Formalism.L2.FormalSeriesBounds.S4.ofFn_prod_apply {F : Type*} [AddCommGroup F] [Module R F] (g : F) :
    ∀ {m : ℕ} (E : Fin m → Module.End R F) (s : Fin m → R), (∀ i, E i g = s i • g) →
      (List.ofFn E).prod g = (∏ i, s i) • g := by sorry
