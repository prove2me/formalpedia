-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_trunc_total
-- name    : Formalism.CyclotomicNorms.residueMatrixData.trunc_total
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:09.309828+00:00
-- url     : https://prove2.me/theorems/88f510ae-b4a5-475f-8756-a7a7da51d001
-- title:
--   residue Matrix Data: trunc total
-- statement:
--   The residue Matrix Data construction uses the trunc total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L174-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L174-L191

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

theorem Formalism.CyclotomicNorms.residueMatrixData.trunc_total (x y : TruncK K' n) : x ∣ y ∨ y ∣ x := by sorry
