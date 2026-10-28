-- Prove2me | solution 1 for gpy_sum_mu_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-28T17:11:31.970545+00:00
-- url     : https://prove2.me/submissions/cf3ffe18-7044-4395-9b37-9995f0a25c54

/-
  Submission file for the Prove2Me problem `gpy_sum_mu_mul_prod`
  (Mobius-weighted divisor sum as Euler product over prime factors,
  squarefree case).

  Self-contained: imports Mathlib only. Contains the verified
  arithmetic-function identity, the plain-function version as a body
  (not a separate problem), the restated theorem, and top-level
  `theorem solution` in the problem's exact binder/statement form
  (statement mechanically extracted from the restated theorem, so the
  two are textually identical). No sorry tactic, no axioms beyond the
  standard ones, no platform imports.
-/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

namespace GPY

theorem sum_mu_mul_eq_prod_of_squarefree {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d
      = ∏ p ∈ n.primeFactors, (1 - f p) := by
  have key := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hn
  rw [key]

theorem sum_mu_mul_fun_eq_prod_of_squarefree {F : ℕ → ℝ} (hF1 : F 1 = 1)
    (hFmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * F d
      = ∏ p ∈ n.primeFactors, (1 - F p) := by
  let f : ArithmeticFunction ℝ := ⟨fun d => if d = 0 then 0 else F d, by simp⟩
  have hf1 : f 1 = 1 := by
    show (if (1 : ℕ) = 0 then (0 : ℝ) else F 1) = 1
    rw [if_neg one_ne_zero]
    exact hF1
  have hfmult : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨hf1, ?_⟩
    intro m n hm hn hmn
    show (if m * n = 0 then (0 : ℝ) else F (m * n))
      = (if m = 0 then (0 : ℝ) else F m) * (if n = 0 then (0 : ℝ) else F n)
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    exact hFmul hmn
  have hfd : ∀ d ∈ n.divisors, f d = F d := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rcases Nat.mem_divisors.mp hd with ⟨hdvd, -⟩
      intro h
      rw [h] at hdvd
      exact hn.ne_zero (by simpa using hdvd)
    show (if d = 0 then (0 : ℝ) else F d) = F d
    rw [if_neg hd0]
  have hfp : ∀ p ∈ n.primeFactors, f p = F p := by
    intro p hp
    have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
    show (if p = 0 then (0 : ℝ) else F p) = F p
    rw [if_neg hp0]
  calc ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * F d
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d :=
        Finset.sum_congr rfl (fun d hd => by rw [hfd d hd])
    _ = ∏ p ∈ n.primeFactors, (1 - f p) :=
        sum_mu_mul_eq_prod_of_squarefree hfmult hn
    _ = ∏ p ∈ n.primeFactors, (1 - F p) :=
        Finset.prod_congr rfl (fun p hp => by rw [hfp p hp])

theorem sum_mu_mul_eq_prod_of_squarefree_restated {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d
      = ∏ p ∈ n.primeFactors, (1 - f p) := by
  exact sum_mu_mul_eq_prod_of_squarefree hf hn

end GPY

theorem solution {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * f d
      = ∏ p ∈ n.primeFactors, (1 - f p) := GPY.sum_mu_mul_eq_prod_of_squarefree_restated hf hn
