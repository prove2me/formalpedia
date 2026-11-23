-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_eq_bot_of_noTorsion
-- name    : Formalism.CyclotomicNorms.residueMatrixData.eq_bot_of_noTorsion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:10.800055+00:00
-- url     : https://prove2.me/theorems/81140fba-2cce-4c09-8a51-95f883eca199
-- title:
--   residue Matrix Data: eq bot of no Torsion
-- statement:
--   The residue Matrix Data construction uses the eq bot of no Torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L244-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L244-L258

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

theorem Formalism.CyclotomicNorms.residueMatrixData.eq_bot_of_noTorsion {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (h : ∀ x ∈ N, (TT) • x = 0 → x = 0) : N = ⊥ := by sorry
