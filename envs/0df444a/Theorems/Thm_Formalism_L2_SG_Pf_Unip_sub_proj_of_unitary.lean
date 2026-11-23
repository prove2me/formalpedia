-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_sub_proj_of_unitary
-- name    : Formalism.L2.SG.Pf.Unip.sub_proj_of_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:15.987075+00:00
-- url     : https://prove2.me/theorems/67110d57-bc0d-46d6-a7bb-abbc547312dc
-- title:
--   Unip: sub proj of unitary
-- statement:
--   The Unip construction uses the sub proj of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L180-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L180-L201

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]
variable {lv : ι → ℕ} {T k : ℕ}
variable {J J' : Matrix ι ι K}
variable [Invertible (2 : K)]

theorem Formalism.L2.SG.Pf.Unip.sub_proj_of_unitary (hJ : Graded lv T J) (hJ' : Graded lv T J') (h : J' * J = 1)
    {x : Matrix ι ι K} (hx : xᴴ * J * x = J) (hx1 : InPat lv k (x - 1)) :
    InPat lv (k + k) ((x - 1) - proj J J' (x - 1)) := by sorry
