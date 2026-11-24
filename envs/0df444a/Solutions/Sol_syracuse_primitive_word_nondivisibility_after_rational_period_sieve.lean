-- Prove2me | solution 1 for syracuse_primitive_word_nondivisibility_after_rational_period_sieve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T07:51:42.306414+00:00
-- url     : https://prove2.me/submissions/40e323b5-02ca-418a-ba9e-1bf50067af13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_cycle_eq_one_of_adjacent_period_sieve
import Theorems.Thm_syracuse_primitive_word_nondivisibility_after_adjacent_period_sieve
import Theorems.Thm_syracuse_positive_affine_word_realization

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
    (hcandidate : 92011 * (50508 * w.length / 31867 + 1) < 145834 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  by_cases hc : 99991 * (50508 * w.length / 31867 + 1) < 158482 * w.length
  · exact syracuse_primitive_word_nondivisibility_after_adjacent_period_sieve w hpositive hlength hprimitive hgap
      hlow hlowSharp hbaselineBudget hrotatedBaseline hsparse hcandidate hc
  · intro hdiv
    obtain ⟨m, hm, hcycle, hword⟩ :=
      syracuse_positive_affine_word_realization w hpositive hgap hdiv
    have hmone := syracuse_cycle_eq_one_of_adjacent_period_sieve m w.length hm (by omega)
      hcycle (Nat.le_of_not_gt hc)
    subst m
    have hfix : syracuseStep 1 = 1 := by decide +kernel
    have hval : (3 * (1 : ℕ) + 1).factorization 2 = 2 := by decide +kernel
    simp only [Function.iterate_fixed hfix, hval, List.ofFn_const] at hword
    have hsum := congrArg List.sum hword
    rw [List.sum_const_nat] at hsum
    omega
