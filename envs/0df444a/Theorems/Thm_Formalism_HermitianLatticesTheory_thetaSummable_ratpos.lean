-- Prove2me | Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_ratpos
-- name    : Formalism.HermitianLatticesTheory.thetaSummable_ratpos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:25.225662+00:00
-- url     : https://prove2.me/theorems/31fd4a0f-3e75-4b3d-b433-fb3457b8cd9f
-- title:
--   Hermitian Lattices Theory: theta Summable ratpos
-- statement:
--   The Hermitian Lattices Theory construction uses the theta Summable ratpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L223-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/HermitianLatticesProofs/ThetaSummable.lean#L223-L253

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

theorem Formalism.HermitianLatticesTheory.thetaSummable_ratpos (G : Matrix ι ι ℚ)
    (hZ : ∀ c : ι → ℤ, c ≠ 0 → 0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ))) :
    ∀ w : ι → ℚ, w ≠ 0 → 0 < w ⬝ᵥ (G *ᵥ w) := by sorry
