-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_mul_eq_inv_mul
-- name    : Formalism.CyclotomicNorms.residueMatrixData.mul_eq_inv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:11.251801+00:00
-- url     : https://prove2.me/theorems/f988d6c9-8024-4ae9-a37f-f596d6b1da02
-- title:
--   residue Matrix Data: mul eq inv mul
-- statement:
--   The residue Matrix Data construction uses the mul eq inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L371-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L371-L373

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

theorem Formalism.CyclotomicNorms.residueMatrixData.mul_eq_inv_mul {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (hP : IsUnit P.det) :
    Φ * Q = P⁻¹ * (P * Φ * Q) := by sorry
