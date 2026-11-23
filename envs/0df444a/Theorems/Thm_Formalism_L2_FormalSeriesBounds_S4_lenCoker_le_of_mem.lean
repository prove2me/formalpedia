-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_lenCoker_le_of_mem
-- name    : Formalism.L2.FormalSeriesBounds.S4.lenCoker_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:01.004829+00:00
-- url     : https://prove2.me/theorems/79b99f4d-417c-4eb1-80c2-49fe3285beb2
-- title:
--   S4: len Coker le of mem
-- statement:
--   The S4 construction uses the len Coker le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L29-L41

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

theorem Formalism.L2.FormalSeriesBounds.S4.lenCoker_le_of_mem (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {m h : ℕ} (B : Matrix (Fin m) (Fin h) R) {x : R} (hx : x ∈ fitt0 B) :
    lenCoker v B ≤ v x := by sorry
