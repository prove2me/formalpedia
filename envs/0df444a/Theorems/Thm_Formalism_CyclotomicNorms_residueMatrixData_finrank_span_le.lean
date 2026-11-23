-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_finrank_span_le
-- name    : Formalism.CyclotomicNorms.residueMatrixData.finrank_span_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:17.198942+00:00
-- url     : https://prove2.me/theorems/89d43a16-cc56-441f-82ca-e14d214b58fb
-- title:
--   residue Matrix Data: finrank span le
-- statement:
--   The residue Matrix Data construction uses the finrank span le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L260-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L260-L288

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

theorem Formalism.CyclotomicNorms.residueMatrixData.finrank_span_le {a m : ℕ} (x : Fin a → TruncK K' n) (hx : (TT) ^ m • x = 0) :
    Module.finrank K' ↥(Submodule.span (TruncK K' n) {x}) ≤ m := by sorry
