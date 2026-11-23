-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_cay_map
-- name    : Formalism.L2.SG.Pf.Unip.cay_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:17.332095+00:00
-- url     : https://prove2.me/theorems/e50a41aa-ce91-44a9-b612-84e9166195ab
-- title:
--   Unip: cay map
-- statement:
--   The Unip construction uses the cay map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L237-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L237-L248

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {lv : ι → ℕ} {k : ℕ}

theorem Formalism.L2.SG.Pf.Unip.cay_map {K' : Type*} [CommRing K'] [Invertible (2 : K')] (f : K →+* K') (N : ℕ) (Z : Matrix ι ι K) :
    (cay N Z).map f = cay N (Z.map f) := by sorry
