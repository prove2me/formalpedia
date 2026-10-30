-- Prove2me | solution 1 for gpy_prime_dvd_lcm
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:36:54.152269+00:00
-- url     : https://prove2.me/submissions/c7a242ac-f9b6-4728-8c77-3f3f927a5799

/- Submission file for `gpy_prime_dvd_lcm` (publish2 good-count batch).
Self-contained: imports Mathlib only.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ Nat.lcm m n) :
    p ∣ m ∨ p ∣ n := by
  by_contra hc
  have hc1 : ¬ p ∣ m := fun h => hc (Or.inl h)
  have hc2 : ¬ p ∣ n := fun h => hc (Or.inr h)
  have hcm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc1
  have hcn : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc2
  have hcop : Nat.Coprime p (m * n) := hcm.mul_right hcn
  have hdvd : Nat.lcm m n ∣ m * n :=
    ⟨Nat.gcd m n, (Nat.gcd_mul_lcm m n).symm.trans (mul_comm _ _)⟩
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop) (dvd_trans h hdvd)
