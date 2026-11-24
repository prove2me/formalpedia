-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_blk
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.zero_of_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:39.721971+00:00
-- url     : https://prove2.me/theorems/ecaf0cec-a4c1-4dbc-974d-e8595c7448ff
-- title:
--   Is UB: zero of blk
-- statement:
--   The Is UB construction uses the zero of blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L19-L22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
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
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}

theorem Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.zero_of_blk {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m}
    (hij : blk i ≠ blk j) : C i j = 0 := by sorry
