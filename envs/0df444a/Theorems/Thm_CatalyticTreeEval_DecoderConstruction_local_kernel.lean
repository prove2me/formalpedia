-- Prove2me | Theorems.Thm_CatalyticTreeEval_DecoderConstruction_local_kernel
-- name    : CatalyticTreeEval.DecoderConstruction.local_kernel
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T01:34:12.337259+00:00
-- url     : https://prove2.me/theorems/df57a867-2f5c-4e0d-a6cc-a1a2aa22f84f
-- title:
--   Three-term local decoder: normalization and cancellation
-- statement:
--   Let R be a commutative ring in which 1 and 2 are nonzero. The three integer-valued local kernels with shifts 0, 1 and 2 sum to one at zero. For every mask z in R, the sum of the kernels at z+c, and also at z+2c, is zero. These identities provide the per-prime normalization and cancellation used in the tensor-product canonical decoder. Cancellation takes place over the integers before reduction modulo the final modulus.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Lemma 3.19, local kernels in its proof.

import Definitions.Def_CatalyticTreeEval_DecoderConstruction
open CatalyticTreeEval.DecoderConstruction
set_option autoImplicit false

theorem CatalyticTreeEval.DecoderConstruction.local_kernel {R : Type} [CommRing R] [DecidableEq R]
    (h1 : (1 : R) ≠ 0) (h2 : (2 : R) ≠ 0) :
    (∑ c : Fin 3, localTerm c (0 : R) = 1) ∧
    (∀ z : R, ∑ c : Fin 3, localTerm c (z + (c.val : R)) = 0) ∧
    (∀ z : R, ∑ c : Fin 3, localTerm c (z + 2 * (c.val : R)) = 0) := by sorry
