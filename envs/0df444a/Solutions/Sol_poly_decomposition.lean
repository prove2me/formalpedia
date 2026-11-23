-- Prove2me | solution 1 for poly_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:41:26.60481+00:00
-- url     : https://prove2.me/submissions/12e695f8-5c45-4f85-96ae-cfab406eebcd

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Semiring F] (P : Polynomial F) (m : ℕ) (hm : m > 0) :
    P = ∑ j : Fin m, (poly_component P m j).comp (Polynomial.X ^ m) * Polynomial.X ^ (j : ℕ) := by
  ext n
  rw [← Nat.div_add_mod n m]
  simp only [poly_component, Polynomial.sum_comp, Polynomial.mul_X_pow_comp, Polynomial.C_comp,
      Finset.sum_mul, mul_assoc, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single ⟨n % m, Nat.mod_lt _ hm⟩]
    <;> simp only [← pow_mul, mul_comm, Finset.mem_univ, not_true_eq_false, ne_eq, forall_const,
      Polynomial.coeff_mul_X_pow, Polynomial.coeff_X_pow, mul_eq_mul_left_iff, mul_ite, mul_one,
      mul_zero, IsEmpty.forall_iff]
  · rw [Finset.sum_eq_single (n / m)]
      <;> simp only [mul_comm m, true_or, ↓reduceIte, Finset.mem_range, ne_eq, ite_eq_right_iff,
        not_lt]
    · grind
    · exact fun h ↦ Polynomial.coeff_eq_zero_of_natDegree_lt <| by
        nlinarith [Nat.div_mul_le_self n m, Nat.zero_le (n % m)]
  · intro b hb
    rw [Finset.sum_eq_zero]
    intro _ _
    simp only [add_comm, ← pow_add, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
      ite_eq_right_iff]
    intro h
    have := congr_arg (· % m) h
    simp [Nat.add_mod, Nat.mod_eq_of_lt b.2] at this
    exact absurd (Fin.ext this.symm) hb
