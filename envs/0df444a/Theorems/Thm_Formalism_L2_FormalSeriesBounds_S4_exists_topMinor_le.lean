-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_exists_topMinor_le
-- name    : Formalism.L2.FormalSeriesBounds.S4.exists_topMinor_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:35.179801+00:00
-- url     : https://prove2.me/theorems/d9b3520d-357e-43fd-aff6-c5ec1a282382
-- title:
--   S4: exists top Minor le
-- statement:
--   The S4 construction uses the exists top Minor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L43-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L43-L69

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

theorem Formalism.L2.FormalSeriesBounds.S4.exists_topMinor_le (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) (n : ℕ) :
    ∀ (k : ℕ) (Y : Matrix (Fin (n + k)) (Fin (n + k)) R),
      ∃ f : Fin n → Fin (n + k), StrictMono f ∧
        v (Y.submatrix (Fin.castAdd k) f).det ≤ v Y.det := by sorry
