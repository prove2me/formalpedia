-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_conj_apply
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.conj_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:19.134798+00:00
-- url     : https://prove2.me/theorems/c1f3fd77-7646-40c7-aad0-5bf994823e9b
-- title:
--   Unitary Standard Vectors: conj apply
-- statement:
--   The Unitary Standard Vectors construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L96-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/ZeroOfBlk.lean#L96-L110

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

theorem Formalism.L2.S.L6.UnitaryStandardVectors.conj_apply (X : Matrix (Fin m) (Fin m) ℂ) (j i : Fin m) :
    (Z * X * Z⁻¹) j i = Z j (π j) * X (π j) (π i) * (Z i (π i))⁻¹ := by sorry
