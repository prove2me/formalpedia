-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_Z_mul_Zi
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.Z_mul_Zi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:11.414035+00:00
-- url     : https://prove2.me/theorems/a0bb4b99-2548-474d-a82a-a5b5156abcf5
-- title:
--   Unitary Standard Vectors: Z mul Zi
-- statement:
--   The Unitary Standard Vectors construction uses the Z mul Zi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L76-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L76-L90

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
variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ

theorem Formalism.L2.S.L6.UnitaryStandardVectors.Z_mul_Zi : Z * Zi π Z = 1 := by sorry
