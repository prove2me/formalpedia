-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_proj_skew
-- name    : Formalism.L2.SG.Pf.Unip.proj_skew
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:32.378531+00:00
-- url     : https://prove2.me/theorems/9b802e8c-0d99-42f7-9e6d-7b67685d9e88
-- title:
--   Unip: proj skew
-- statement:
--   The Unip construction uses the proj skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L163-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L163-L173

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

theorem Formalism.L2.SG.Pf.Unip.proj_skew (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (h : J' * J = 1) (h' : J * J' = 1) (M : Matrix ι ι K) :
    (proj J J' M)ᴴ * J = -(J * proj J J' M) := by sorry
