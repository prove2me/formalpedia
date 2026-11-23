-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_cyclic_of_socle
-- name    : Formalism.CyclotomicNorms.residueMatrixData.cyclic_of_socle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:56.453078+00:00
-- url     : https://prove2.me/theorems/75bb8126-b1af-4312-b6ae-421d0fd67fb0
-- title:
--   residue Matrix Data: cyclic of socle
-- statement:
--   The residue Matrix Data construction uses the cyclic of socle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L297-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L297-L362

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

theorem Formalism.CyclotomicNorms.residueMatrixData.cyclic_of_socle {a : ℕ} (N : Submodule (TruncK K' n) (Fin a → TruncK K' n))
    (hN : Module.finrank K' ↥(N ⊓ LinearMap.ker ((TT) • LinearMap.id :
          (Fin a → TruncK K' n) →ₗ[TruncK K' n] (Fin a → TruncK K' n))) ≤ 1) :
    ∃ x, N = Submodule.span (TruncK K' n) {x} := by sorry
