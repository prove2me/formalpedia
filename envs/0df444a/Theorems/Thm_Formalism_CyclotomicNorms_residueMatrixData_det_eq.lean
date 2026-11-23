-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_det_eq
-- name    : Formalism.CyclotomicNorms.residueMatrixData.det_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:06.52921+00:00
-- url     : https://prove2.me/theorems/7d728a4d-5ec6-4d0a-bb70-237c5a3d9264
-- title:
--   residue Matrix Data: det eq
-- statement:
--   The residue Matrix Data construction uses the det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L440-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L440-L443

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

theorem Formalism.CyclotomicNorms.residueMatrixData.det_eq {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) :
    P.det * Φ.det * Q.det = (TT) ^ (∑ i, k i) := by sorry
