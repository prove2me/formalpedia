-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_exists_diag
-- name    : Formalism.CyclotomicNorms.residueMatrixData.exists_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:26.658653+00:00
-- url     : https://prove2.me/theorems/a7531022-8fd3-4faa-b343-a3528f4c5585
-- title:
--   residue Matrix Data: exists diag
-- statement:
--   The residue Matrix Data construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L68-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L68-L136

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
variable {R : Type*} [CommRing R]

theorem Formalism.CyclotomicNorms.residueMatrixData.exists_diag (hR : ∀ x y : R, x ∣ y ∨ y ∣ x) : ∀ (a : ℕ) (M : Matrix (Fin a) (Fin a) R),
    ∃ P Q : Matrix (Fin a) (Fin a) R, IsUnit P.det ∧ IsUnit Q.det ∧
      ∃ d : Fin a → R, P * M * Q = diagonal d := by sorry
