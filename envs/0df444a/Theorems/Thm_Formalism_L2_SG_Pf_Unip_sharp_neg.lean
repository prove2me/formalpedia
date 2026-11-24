-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_sharp_neg
-- name    : Formalism.L2.SG.Pf.Unip.sharp_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:31.927823+00:00
-- url     : https://prove2.me/theorems/2c604ffe-35ee-43a3-9024-67c4a7a9244f
-- title:
--   Unip: sharp neg
-- statement:
--   The Unip construction uses the sharp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L118-L119

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

theorem Formalism.L2.SG.Pf.Unip.sharp_neg (M : Matrix ι ι K) : sharp J J' (-M) = -sharp J J' M := by sorry
