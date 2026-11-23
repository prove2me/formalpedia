-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_ker_lower
-- name    : Formalism.CyclotomicNorms.residueMatrixData.ker_lower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:05.202283+00:00
-- url     : https://prove2.me/theorems/e4bdc90b-9b59-48c3-bf27-7e3b56acb30b
-- title:
--   residue Matrix Data: ker lower
-- statement:
--   The residue Matrix Data construction uses the ker lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L375-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L375-L420

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

theorem Formalism.CyclotomicNorms.residueMatrixData.ker_lower {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hk : ∀ i, k i ≤ n) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    ∑ i, k i ≤ Module.finrank K' ↥(LinearMap.ker (Matrix.toLin' Φ)) := by sorry
