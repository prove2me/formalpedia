-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_gram_isUnit
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.gram_isUnit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:26.184083+00:00
-- url     : https://prove2.me/theorems/ea04ed47-fc84-40e9-8574-027297cb4ce7
-- title:
--   Unitary Standard Vectors: gram is Unit
-- statement:
--   The Unitary Standard Vectors construction uses the gram is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LastDiagMulVec.lean#L23-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LastDiagMulVec.lean#L23-L72

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

theorem Formalism.L2.S.L6.UnitaryStandardVectors.gram_isUnit (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hZ : IsUnit Z.det) (T T' : ℝ)
    (hG : 1 - (T : ℂ) * T' * (Z⁻¹ (Fin.last r) (Fin.last r) * starRingEnd ℂ (Z⁻¹ (Fin.last r) (Fin.last r))) ≠ 0) :
    IsUnit (Matrix.fromBlocks (lastDiag (-(T : ℂ))) Z Zᴴ (lastDiag (-(T' : ℂ)))).det := by sorry
