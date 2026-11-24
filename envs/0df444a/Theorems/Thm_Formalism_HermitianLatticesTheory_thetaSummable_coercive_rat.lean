-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_coercive_rat
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_coercive_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:10.632631+00:00
-- url     : https://prove2.me/theorems/16edf4c3-6711-4695-8ab5-abfc584921eb
-- title:
--   Hermitian Lattices Theory: theta Summable coercive rat
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable coercive rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L275-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L275-L285

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.HermitianLatticesTheory.thetaSummable_coercive_rat (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ w : ι → ℚ, l * ∑ i, ((w i : ℚ) : ℝ) ^ 2 ≤ ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by sorry
