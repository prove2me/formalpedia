-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_rankUpdate_mul
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.rankUpdate_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:04.078492+00:00
-- url     : https://prove2.me/theorems/4004fae9-239c-4683-8dba-a86def8a13dd
-- title:
--   Unitary Standard Vectors: rank Update mul
-- statement:
--   The Unitary Standard Vectors construction uses the rank Update mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RankUpdateMul.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RankUpdateMul.lean#L14-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RankUpdateMul
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
variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.L2.S.L6.UnitaryStandardVectors.rankUpdate_mul (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (hΓ : IsUnit (Wᴴ * J * W).det) :
    Ymat J W M * W = W * (1 + M) := by sorry
