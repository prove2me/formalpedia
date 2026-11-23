-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_notMem
-- name    : Formalism.CyclotomicNorms.residueMatrixData.tt_pow_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:28.72143+00:00
-- url     : https://prove2.me/theorems/d86032a7-b911-4499-8bb1-79ee97d3ee9b
-- title:
--   residue Matrix Data: tt pow not Mem
-- statement:
--   The residue Matrix Data construction uses the tt pow not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L193-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L193-L208

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

theorem Formalism.CyclotomicNorms.residueMatrixData.tt_pow_notMem {m C : ℕ} (hm : m ≤ C) (hC : C < n) :
    (TT) ^ m ∉ Ideal.span {(TT) ^ (C + 1)} := by sorry
