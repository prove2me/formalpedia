-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_exists_strictMono_minor
-- name    : Formalism.L2.FormalSeriesBounds.S4.exists_strictMono_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:51.9208+00:00
-- url     : https://prove2.me/theorems/3f058da5-9d47-4423-8e6d-4e6a3748ce4b
-- title:
--   S4: exists strict Mono minor
-- statement:
--   The S4 construction uses the exists strict Mono minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L71-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L71-L93

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

theorem Formalism.L2.FormalSeriesBounds.S4.exists_strictMono_minor (v : AddValuation R (WithTop ℝ)) {n h : ℕ}
    (B : Matrix (Fin n) (Fin h) R) (g : Fin n → Fin h) (hg : (B.submatrix id g).det ≠ 0) :
    ∃ f : Fin n → Fin h, StrictMono f ∧ v (B.submatrix id f).det = v (B.submatrix id g).det := by sorry
