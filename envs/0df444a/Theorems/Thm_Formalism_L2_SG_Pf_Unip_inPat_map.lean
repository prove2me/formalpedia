-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_inPat_map
-- name    : Formalism.L2.SG.Pf.Unip.inPat_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:02.81586+00:00
-- url     : https://prove2.me/theorems/15dd0988-ba23-41ab-b6e8-ae74086fa591
-- title:
--   Unip: in Pat map
-- statement:
--   The Unip construction uses the in Pat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L77-L79

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
variable {lv : ι → ℕ} {k l : ℕ} {Z W : Matrix ι ι K}

theorem Formalism.L2.SG.Pf.Unip.inPat_map {K' : Type*} [CommRing K'] (f : K →+* K') (hZ : InPat lv k Z) : InPat lv k (Z.map f) := by sorry
