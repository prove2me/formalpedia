-- Prove2me | Theorems.Thm_Formalism_REAL_mul_exp_neg_polarLog_mem_compact
-- name    : Formalism.REAL.mul_exp_neg_polarLog_mem_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:29.666971+00:00
-- url     : https://prove2.me/theorems/01d88be1-3e71-4f64-ac24-2f69026a6640
-- title:
--   REAL: mul exp neg polar Log mem compact
-- statement:
--   The REAL construction uses the mul exp neg polar Log mem compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L187-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IndefiniteUnitaryPreservesForm.lean#L187-L221

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}

theorem Formalism.REAL.mul_exp_neg_polarLog_mem_compact {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    g * NormedSpace.exp (-polarLog g) ∈ Kset ε := by sorry
