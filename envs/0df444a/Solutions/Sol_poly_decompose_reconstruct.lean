-- Prove2me | solution 1 for poly_decompose_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:55.367934+00:00
-- url     : https://prove2.me/submissions/2a1dae76-9f69-413b-b6cf-36de39cdb4f2

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [DecidableEq F]
theorem _root_.solution (m : ℕ) (hm : m > 0) (p : Polynomial F) :
    p = ∑ i : Fin m, (poly_decompose m p i).comp (Polynomial.X ^ m) * Polynomial.X ^ (i : ℕ) := by
  ext x
  rw [Finset.sum_congr rfl fun i _ ↦ by erw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]]
  simp only [← pow_mul, Finset.sum_mul .., Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single ⟨x % m, Nat.mod_lt _ hm⟩]
  · simp only [mul_assoc, ← pow_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (x / m)]
    · rw [if_pos (by rw [Nat.div_add_mod])]
      by_cases hx : x / m < (p.natDegree + 1) / m + 1
      · simp_all only [poly_decompose, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
            Finset.mem_range, ↓reduceIte, Nat.div_add_mod']
      · simp_all only [poly_decompose, not_lt, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
            Finset.mem_range]
        have : p.natDegree < x := by
          nlinarith [Nat.div_mul_le_self x m, Nat.div_add_mod x m, Nat.mod_lt x hm,
            Nat.div_add_mod (p.natDegree + 1) m, Nat.mod_lt (p.natDegree + 1) hm]
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, if_neg hx.not_gt]
    · exact fun b hb hb' ↦ if_neg fun h ↦ hb' <| by nlinarith [Nat.mod_add_div x m, Nat.mod_lt x hm]
    · intro hx
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt] <;> grind
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · intro _
      simp_all only [Finset.mem_univ, ne_eq, Finset.mem_range, mul_assoc, ← pow_add,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero,
          ite_eq_right_iff]
      intro hx
      contrapose! hb
      ext
      simp_all only [ne_eq, Nat.mul_add_mod_self_left, Fin.is_lt, Nat.mod_eq_of_lt]
  · exact fun h ↦ (h <| Finset.mem_univ _).elim
