-- Prove2me | solution 1 for syracuse_primitive_word_residual_unbalanced_windows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T23:28:23.528003+00:00
-- url     : https://prove2.me/submissions/0c8fb38d-4715-4b28-810e-61d9785126ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_nontrivial_period_coordinates_at_247463936
import Theorems.Thm_syracuse_primitive_word_residual_period_coordinates_at_247463936
import Theorems.Thm_syracuse_positive_affine_word_realization
import Mathlib.Algebra.BigOperators.Fin

/-
  The realization step follows the accepted Prove2me reduction of
  syracuse_primitive_word_residual_farey_coordinates (theorem 89e43502-29fa-4758-8be2-9c4cffa08d66)
  by user immiq, Apache-2.0 via the Prove2me terms.
-/

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
    (hlarge : 73297 * (50508 * w.length / 31867 + 1) < 116173 * w.length)
    (hcoords : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 665*a + 10946*b ∧ w.sum = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 10*b < 3*a)
    (hunbalanced : ∃ i j n : ℕ, i < w.length ∧ j < w.length ∧ 0 < n ∧ n < w.length ∧
      ((w.rotate i).take n).sum + 2 ≤ ((w.rotate j).take n).sum) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  by_cases hc : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      w.length = 31867*a + 15601*b ∧ w.sum = 50508*a + 24727*b
  · exact syracuse_primitive_word_residual_period_coordinates_at_247463936 w hpositive hlength hprimitive hgap hlow hlowSharp hbaselineBudget hrotatedBaseline hsparse hcandidate hadj htriple hlarge hcoords hunbalanced hc
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
    have h := syracuse_nontrivial_period_coordinates_at_247463936 m w.length hm (by omega) hcycle hn
    dsimp only at h
    rw [hsum] at h
    exact hc h.2
