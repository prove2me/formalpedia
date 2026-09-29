-- Prove2me | solution 1 for mme_sixSymmetrization_MMObj_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:40:32.037879+00:00
-- url     : https://prove2.me/submissions/eb241c66-e15d-4a94-abfd-a7bec5da25e2

import Mathlib.Tactic
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.SixSymmetrizationMMObj

theorem permAut_MMq_sq
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorQ.permAut (cyclicPerm.trans cyclicPerm) (MMq K n m p) =
      MMq K m p n := by
  show TensorQ.toQ
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (MMObj K n m p)) =
    TensorQ.toQ (MMObj K m p n)
  exact Quotient.sound (mme_MMObj_permObj_cyclic_sq n m p)

theorem permAut_MMq_swapFirstTwo
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorQ.permAut swapFirstTwoPerm (MMq K n m p) =
      MMq K p m n := by
  show TensorQ.toQ
      (TensorObj.permObj swapFirstTwoPerm (MMObj K n m p)) =
    TensorQ.toQ (MMObj K p m n)
  exact Quotient.sound (mme_MMObj_permObj_swapFirstTwo n m p)

theorem toQ_cyclicSymmetrization_MMObj
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorQ.toQ (cyclicSymmetrization (MMObj K n m p)) =
      MMq K (n * m * p) (n * m * p) (n * m * p) := by
  rw [cyclicSymmetrization_eq_public_perm]
  rw [TensorQ.toQ_kron, TensorQ.toQ_kron]
  rw [← TensorQ.permAut_toQ, ← TensorQ.permAut_toQ]
  rw [permAut_MMq]
  change MMq K n m p *
      (MMq K p n m *
        TensorQ.permAut (cyclicPerm.trans cyclicPerm) (MMq K n m p)) = _
  rw [permAut_MMq_sq]
  rw [MMq_mul, MMq_mul]
  congr 1 <;> ring

end MME.SixSymmetrizationMMObj

/-- The full six-symmetrization of one rectangular matrix-multiplication
tensor is a square matrix-multiplication tensor whose side is the square of
the original volume. -/
theorem solution
    {K : Type u} [Field K] (n m p : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization (MMObj K n m p))
      (MMObj K ((n * m * p) ^ 2) ((n * m * p) ^ 2)
        ((n * m * p) ^ 2)) := by
  apply (TensorQ.toQ_eq_iff).1
  unfold sixSymmetrization
  rw [TensorQ.toQ_kron]
  rw [MME.SixSymmetrizationMMObj.toQ_cyclicSymmetrization_MMObj]
  rw [← TensorQ.permAut_toQ]
  rw [MME.SixSymmetrizationMMObj.toQ_cyclicSymmetrization_MMObj]
  rw [MME.SixSymmetrizationMMObj.permAut_MMq_swapFirstTwo]
  rw [MMq_mul]
  simp only [pow_two]
  rfl
