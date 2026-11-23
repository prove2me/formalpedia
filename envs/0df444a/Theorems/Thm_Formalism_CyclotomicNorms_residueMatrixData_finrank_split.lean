-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_finrank_split
-- name    : Formalism.CyclotomicNorms.residueMatrixData.finrank_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:59.258449+00:00
-- url     : https://prove2.me/theorems/2e344f96-00cf-489f-add7-d1bd0bbb7d83
-- title:
--   residue Matrix Data: finrank split
-- statement:
--   The residue Matrix Data construction uses the finrank split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L237-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L237-L242

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open Formalism.CyclotomicNorms.residueMatrixData
variable {K' : Type} [Field K'] {n : ℕ}
local notation "TT" => (Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X : TruncK K' n)

theorem Formalism.CyclotomicNorms.residueMatrixData.finrank_split {a : ℕ} (W N : Submodule (TruncK K' n) (Fin a → TruncK K' n)) (h : N ≤ W) :
    Module.finrank K' (W ⧸ N.comap W.subtype) + Module.finrank K' N = Module.finrank K' W := by sorry
