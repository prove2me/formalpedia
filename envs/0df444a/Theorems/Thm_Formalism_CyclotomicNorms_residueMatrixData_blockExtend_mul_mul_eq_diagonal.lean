-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_mul_mul_eq_diagonal
-- name    : Formalism.CyclotomicNorms.residueMatrixData.blockExtend_mul_mul_eq_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:07.807802+00:00
-- url     : https://prove2.me/theorems/939e27ce-53ae-4cd4-8e1e-29d9866aa8fe
-- title:
--   residue Matrix Data: block Extend mul mul eq diagonal
-- statement:
--   The residue Matrix Data construction uses the block Extend mul mul eq diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L49-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/ResModule.lean#L49-L63

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

theorem Formalism.CyclotomicNorms.residueMatrixData.blockExtend_mul_mul_eq_diagonal {a : ℕ} (P Q : Matrix (Fin a) (Fin a) R) (E : Matrix (Fin (a+1)) (Fin (a+1)) R)
    (h1 : ∀ j : Fin a, E 0 j.succ = 0) (h2 : ∀ i : Fin a, E i.succ 0 = 0) (d : Fin a → R)
    (hd : P * (Matrix.of fun i j : Fin a => E i.succ j.succ) * Q = diagonal d) :
    ext1 P * E * ext1 Q = diagonal (Fin.cons (E 0 0) d) := by sorry
