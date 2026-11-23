-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_proj
-- name    : Formalism.L2.SG.Pf.Unip.inPat_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:25.441752+00:00
-- url     : https://prove2.me/theorems/eec9d29a-41fe-471c-b5e9-4dd990fd13f6
-- title:
--   Unip: in Pat proj
-- statement:
--   The Unip construction uses the in Pat proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L158-L161

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

theorem Formalism.L2.SG.Pf.Unip.inPat_proj (hJ : Graded lv T J) (hJ' : Graded lv T J') {M : Matrix ι ι K} (hM : InPat lv k M) :
    InPat lv k (proj J J' M) := by sorry
