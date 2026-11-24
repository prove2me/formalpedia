-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_proj_of_skew
-- name    : Formalism.L2.SG.Pf.Unip.proj_of_skew
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:23.435443+00:00
-- url     : https://prove2.me/theorems/2adc718b-fa38-40d8-b02e-9beacd5bd6bf
-- title:
--   Unip: proj of skew
-- statement:
--   The Unip construction uses the proj of skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L175-L178

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

theorem Formalism.L2.SG.Pf.Unip.proj_of_skew (h : J' * J = 1) {X : Matrix ι ι K} (hX : Xᴴ * J = -(J * X)) :
    proj J J' X = X := by sorry
