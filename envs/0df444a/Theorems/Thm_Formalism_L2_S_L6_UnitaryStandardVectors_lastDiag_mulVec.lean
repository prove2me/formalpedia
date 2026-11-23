-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_lastDiag_mulVec
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.lastDiag_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:49.083057+00:00
-- url     : https://prove2.me/theorems/3734d94d-1403-4859-81cd-ae3a24fcd9b7
-- title:
--   Unitary Standard Vectors: last Diag mul Vec
-- statement:
--   The Unitary Standard Vectors construction uses the last Diag mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LastDiagMulVec.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LastDiagMulVec.lean#L15-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LastDiagMulVec
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
variable {r : ℕ}

theorem Formalism.L2.S.L6.UnitaryStandardVectors.lastDiag_mulVec (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by sorry
