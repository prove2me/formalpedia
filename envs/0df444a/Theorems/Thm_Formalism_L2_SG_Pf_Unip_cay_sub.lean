-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_cay_sub
-- name    : Formalism.L2.SG.Pf.Unip.cay_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:24.423845+00:00
-- url     : https://prove2.me/theorems/bbe8861b-8b1b-4e8d-bbf6-ce5e31fe7446
-- title:
--   Unip: cay sub
-- statement:
--   The Unip construction uses the cay sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipTool.lean#L224-L229

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

theorem Formalism.L2.SG.Pf.Unip.cay_sub (N : ℕ) {Z : Matrix ι ι K} (hZ : InPat lv k Z) : InPat lv (k + k) (cay (N + 1) Z - 1 - Z) := by sorry
