-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_sharp
-- name    : Formalism.L2.SG.Pf.Unip.inPat_sharp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:50.291146+00:00
-- url     : https://prove2.me/theorems/80e9a553-433b-48eb-bb59-b1ad192233a7
-- title:
--   Unip: in Pat sharp
-- statement:
--   The Unip construction uses the in Pat sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L93-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L93-L108

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

theorem Formalism.L2.SG.Pf.Unip.inPat_sharp {J J' Z : Matrix ι ι K} (hJ : Graded lv T J) (hJ' : Graded lv T J') (hZ : InPat lv k Z) :
    InPat lv k (sharp J J' Z) := by sorry
