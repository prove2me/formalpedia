-- Prove2me | Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_Ymat_sub
-- name    : Formalism.L2.S.L6.UnitaryStandardVectors.Ymat_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:31.57844+00:00
-- url     : https://prove2.me/theorems/9e1c03f2-3621-488f-b655-b6605baf18a8
-- title:
--   Unitary Standard Vectors: Ymat sub
-- statement:
--   The Unitary Standard Vectors construction uses the Ymat sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RankUpdateMul.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RankUpdateMul.lean#L23-L27

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

theorem Formalism.L2.S.L6.UnitaryStandardVectors.Ymat_sub (J : Matrix n n ℂ) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ) (x : n → ℂ) :
    Ymat J W M *ᵥ x - x = W *ᵥ (M *ᵥ ((Wᴴ * J * W)⁻¹ *ᵥ ((Wᴴ * J) *ᵥ x))) := by sorry
