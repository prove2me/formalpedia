-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_lt
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.zero_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:40.438218+00:00
-- url     : https://prove2.me/theorems/1912a055-6385-4244-bd00-c9192409469d
-- title:
--   Is UB: zero of lt
-- statement:
--   The Is UB construction uses the zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L14-L17

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

theorem Formalism.L2.S.L6.UnitaryStandardVectors.IsUB.zero_of_lt {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m} (hij : j < i) :
    C i j = 0 := by sorry
