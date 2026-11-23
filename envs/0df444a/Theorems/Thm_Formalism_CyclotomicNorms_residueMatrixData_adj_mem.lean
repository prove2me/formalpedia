-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_adj_mem
-- name    : Formalism.CyclotomicNorms.residueMatrixData.adj_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:24.113054+00:00
-- url     : https://prove2.me/theorems/62e735ef-8fe4-45f4-b749-f6abbbd5aef9
-- title:
--   residue Matrix Data: adj mem
-- statement:
--   The residue Matrix Data construction uses the adj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L445-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L445-L460

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

theorem Formalism.CyclotomicNorms.residueMatrixData.adj_mem {a : ℕ} (Φ P Q : Matrix (Fin a) (Fin a) (TruncK K' n)) (k : Fin a → ℕ)
    (hD : P * Φ * Q = diagonal (fun i => (TT) ^ k i)) (I : Ideal (TruncK K' n))
    (hI : ∀ i j, adjugate Φ i j ∈ I) (i0 : Fin a) :
    (TT) ^ (∑ j ∈ Finset.univ.erase i0, k j) ∈ I := by sorry
