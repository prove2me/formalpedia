-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_coercive
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_coercive
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:30.296961+00:00
-- url     : https://prove2.me/theorems/717c3ee7-c127-4633-8fd2-8b53e154b3af
-- title:
--   Hermitian Lattices Theory: theta Summable coercive
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L116-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L116-L215

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

theorem Formalism.HermitianLatticesTheory.thetaSummable_coercive (G : Matrix ι ι ℚ)
    (hG : ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w)) :
    ∃ l : ℝ, 0 < l ∧ ∀ v : ι → ℝ, l * ‖v‖ ^ 2 ≤ v ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ v) := by sorry
