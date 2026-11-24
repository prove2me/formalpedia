-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_castform
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_castform
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:37.584769+00:00
-- url     : https://prove2.me/theorems/8abebcca-fc15-4d24-9744-c2fad1b1ff5c
-- title:
--   Hermitian Lattices Theory: theta Summable castform
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable castform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L255-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L255-L273

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

theorem Formalism.HermitianLatticesTheory.thetaSummable_castform (G : Matrix ι ι ℚ) (w : ι → ℚ) :
    (fun i => (w i : ℝ)) ⬝ᵥ ((G + Gᵀ).map (Rat.cast : ℚ → ℝ) *ᵥ fun i => (w i : ℝ)) =
      2 * ((w ⬝ᵥ (G *ᵥ w) : ℚ) : ℝ) := by sorry
