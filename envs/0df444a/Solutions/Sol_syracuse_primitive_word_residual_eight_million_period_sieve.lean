-- Prove2me | solution 1 for syracuse_primitive_word_residual_eight_million_period_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T10:16:16.335123+00:00
-- url     : https://prove2.me/submissions/802efae5-97ce-4288-8d98-31d3d2405129
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_nontrivial_period_farey_coordinates
import Theorems.Thm_syracuse_primitive_word_residual_farey_coordinates
import Theorems.Thm_syracuse_positive_affine_word_realization
import Mathlib.Algebra.BigOperators.Fin

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 7621 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2887463 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d))
    (hsparse : (w.length = 7621 ∧ w.sum = 12079) ∨ 8286 ≤ w.length)
    (hcandidate : 92011 * (50508 * w.length / 31867 + 1) < 145834 * w.length)
    (hadj : 99991 * (50508 * w.length / 31867 + 1) < 158482 * w.length)
    (htriple : 69866 * (50508 * w.length / 31867 + 1) < 110735 * w.length)
    (hlarge : 73297 * (50508 * w.length / 31867 + 1) < 116173 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  by_cases hc : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 665*a + 10946*b ∧ w.sum = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 2*b ≤ 13*a
  · exact syracuse_primitive_word_residual_farey_coordinates w hpositive hlength hprimitive hgap
      hlow hlowSharp hbaselineBudget hrotatedBaseline hsparse hcandidate hadj htriple hlarge hc
  · intro hdiv
    obtain ⟨m, hm, hcycle, hword⟩ := syracuse_positive_affine_word_realization w hpositive hgap hdiv
    have hn : m ≠ 1 := by
      intro he
      subst m
      have hfix : syracuseStep 1 = 1 := by decide +kernel
      have hval : (3*(1 : ℕ)+1).factorization 2 = 2 := by decide +kernel
      simp only [Function.iterate_fixed hfix, hval, List.ofFn_const] at hword
      have hs := congrArg List.sum hword
      rw [List.sum_const_nat] at hs
      omega
    have hsum := congrArg List.sum hword
    rw [List.sum_ofFn, Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (3*syracuseStep^[i] m+1).factorization 2) w.length] at hsum
    have h := syracuse_nontrivial_period_farey_coordinates m w.length hm (by omega) hcycle hn
    dsimp only at h
    rw [hsum] at h
    exact hc h
