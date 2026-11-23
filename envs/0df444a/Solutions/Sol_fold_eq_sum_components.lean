-- Prove2me | solution 1 for fold_eq_sum_components
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T09:04:56.349499+00:00
-- url     : https://prove2.me/submissions/ef14186a-304e-4f46-96b2-f8da21ac7642

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem AuxF_card {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F)
    (hm : m > 0) : (Block D m z).card ≤ m := by
  unfold Block
  calc (D.filter fun y => y ^ m = z).card ≤ (Polynomial.nthRoots m z).toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter] at hy
        simpa [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm] using hy.2
    _ ≤ (Polynomial.nthRoots m z).card := Multiset.toFinset_card_le _
    _ ≤ m := Polynomial.card_nthRoots m z

theorem AuxF_eval {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (hm : m > 0)
    (f : F → F) (z x : F) :
    (Lagrange.interpolate (Block D m z) id f).eval x =
      ∑ i : Fin m, (Lagrange.interpolate (Block D m z) id f).coeff i * x ^ (i : ℕ) := by
  have hdeg : (Lagrange.interpolate (Block D m z) id f).degree < m := by
    calc _ < ((Block D m z).card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ (fun a _ b _ h => h)
      _ ≤ m := by exact_mod_cast AuxF_card D m z hm
  have hnd : (Lagrange.interpolate (Block D m z) id f).natDegree < m := by
    by_cases hp : Lagrange.interpolate (Block D m z) id f = 0
    · rw [hp]; simpa using hm
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
  rw [Polynomial.eval_eq_sum_range' hnd]
  exact (Fin.sum_univ_eq_sum_range (fun i => (Lagrange.interpolate (Block D m z) id f).coeff i * x ^ i) m).symm


theorem fold_eq_sum_components {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (alpha : F) (z : F) :
    Fold D m f alpha z = ∑ i : Fin m, (alpha ^ (i : ℕ)) * folding_component D m f i z := by
  unfold Fold folding_component
  rw [AuxF_eval D m hm]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ)
    (hm : m > 0) (f : F → F) (alpha : F) (z : F) :
    Fold D m f alpha z = ∑ i : Fin m, (alpha ^ (i : ℕ)) * folding_component D m f i z := by
  unfold Fold folding_component
  rw [AuxF_eval D m hm]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
