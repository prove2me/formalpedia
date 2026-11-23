-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_step_mat
-- name    : Formalism.L2.SG.Pf.Unip.step_mat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:50.201294+00:00
-- url     : https://prove2.me/theorems/4bf3e77b-2b60-4fa3-81de-311fc96f1b2d
-- title:
--   Unip: step mat
-- statement:
--   The Unip construction uses the step mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L352-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L352-L369

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
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
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K] [Invertible (2 : K)] {T : ℕ} {J J' : Matrix ι ι K}

theorem Formalism.L2.SG.Pf.Unip.step_mat (hJ : Graded lv T J) (hJ' : Graded lv T J') (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (h : J' * J = 1) (h' : J * J' = 1) (N : ℕ) {x Y : Matrix ι ι K} (hx : xᴴ * J * x = J)
    (hx1 : InPat lv k (x - 1)) (hY : InPat lv k Y) (hYs : Yᴴ * J = -(J * Y)) :
    InPat lv (k + k) (sharp J J' (cay (N + 1) Y) * x *
      sharp J J' (cay (N + 1) (proj J J' (x - 1) - Y)) - 1) := by sorry
