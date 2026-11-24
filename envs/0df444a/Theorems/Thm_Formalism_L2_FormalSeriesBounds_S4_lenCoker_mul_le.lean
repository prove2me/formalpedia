-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_lenCoker_mul_le
-- name    : Formalism.L2.FormalSeriesBounds.S4.lenCoker_mul_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:35.623878+00:00
-- url     : https://prove2.me/theorems/f77b0f8c-6bb8-4c3e-b442-fe74e54f072f
-- title:
--   S4: len Coker mul le
-- statement:
--   The S4 construction uses the len Coker mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L95-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L95-L157

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

theorem Formalism.L2.FormalSeriesBounds.S4.lenCoker_mul_le (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) : lenCoker v (S * α) ≤ lenCoker v α := by sorry
