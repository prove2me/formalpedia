-- Prove2me | solution 1 for honest_fold_preserves_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:45:01.60706+00:00
-- url     : https://prove2.me/submissions/6a351c0b-eb7e-42d9-972e-34dc4b779805

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness
import Theorems.Thm_folded_poly_degree_le
import Theorems.Thm_fold_eq_folded_poly_eval
import Theorems.Thm_FRI_degree_succ_eq
import Theorems.Thm_FRI_domain_foldable
import Theorems.Thm_m_dvd_FRI_degree


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin P.num_foldings)
    (f : FRI_domain P i → F) (h_f_in_code : f ∈ FRI_code P i)
    (alpha : F) :
    FRI_honest_fold P i f alpha ∈ FRI_code P (i + 1) := by
  -- Unfold definitions and extract polynomial
  unfold FRI_honest_fold
  simp only [FRI_code, reedSolomon, Submodule.mem_map] at h_f_in_code ⊢
  obtain ⟨p, hp_deg, hp_eval⟩ := h_f_in_code

  -- The folded polynomial will witness membership in the next code
  refine ⟨folded_poly (P.m i) p alpha, ?_, ?_⟩
  · -- Show degree bound: deg(folded_poly) < d_{i+1} = d_i / m_i
    rw [Polynomial.mem_degreeLT, FRI_degree_succ_eq P i i.isLt]
    have hp_deg' := Polynomial.mem_degreeLT.mp hp_deg
    by_cases hp_zero' : p = 0
    · -- When p = 0, folded_poly is also 0
      have h_folded_zero : folded_poly (P.m i) p alpha = 0 := by
        simp only [hp_zero', folded_poly, poly_decompose, Polynomial.coeff_zero,
                   Polynomial.natDegree_zero, Nat.zero_add, mul_zero, Polynomial.C_0, zero_mul,
                   Finset.sum_const_zero]
      rw [h_folded_zero, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · -- For non-zero p
      have hp_natdeg : p.natDegree < FRI_degree P i := by
        rwa [Polynomial.degree_eq_natDegree hp_zero', Nat.cast_lt] at hp_deg'
      calc (folded_poly (P.m i) p alpha).degree
          ≤ (folded_poly (P.m i) p alpha).natDegree := Polynomial.degree_le_natDegree
        _ ≤ p.natDegree / P.m i := by
          exact_mod_cast folded_poly_degree_le (P.m i) (P.h_m_pos i) p alpha
        _ ≤ (FRI_degree P i - 1) / P.m i := by
          exact_mod_cast Nat.div_le_div_right (Nat.le_sub_one_iff_lt
            (Nat.zero_lt_of_lt hp_natdeg) |>.mpr hp_natdeg)
        _ < FRI_degree P i / P.m i := by
          -- (d-1)/m < d/m follows from m ∣ d
          exact_mod_cast Nat.div_lt_div_of_lt_of_dvd (m_dvd_FRI_degree P i)
            (Nat.sub_one_lt ((Nat.zero_le _).trans_lt hp_natdeg).ne')

  · -- Show evaluation equality
    ext ⟨z, hz⟩
    simp only [evalOn]

    -- Key fact: Fold of p.eval equals the folded polynomial's evaluation
    have h_fold_eq : Fold (FRI_domain P i) (P.m i) (fun x ↦ p.eval x) alpha z =
        (folded_poly (P.m i) p alpha).eval z :=
      fold_eq_folded_poly_eval (FRI_domain P i) (P.m i) (P.h_m_pos i) p alpha z
        ((FRI_domain_succ_eq P i i.isLt).symm ▸ hz) (FRI_domain_foldable P i)

    -- extend_by_zero f agrees with p.eval on the domain
    have h_f_eq_p : ∀ x ∈ FRI_domain P i, extend_by_zero (FRI_domain P i) f x = p.eval x := by
      intro x hx
      simp only [extend_by_zero, hx, dite_true]
      simpa only [evalOn, LinearMap.coe_mk, AddHom.coe_mk] using (congr_fun hp_eval ⟨x, hx⟩).symm

    -- Fold only depends on values in Block(z) ⊆ D_i, so Fold(extend_by_zero f) = Fold(p.eval)
    change (folded_poly (P.m i) p alpha).eval z =
      Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f) alpha z
    rw [← h_fold_eq, Fold]
    congr 1
    apply Lagrange.interpolate_eq_of_values_eq_on
    intro x hx
    exact (h_f_eq_p x (Finset.mem_filter.mp hx).1).symm
