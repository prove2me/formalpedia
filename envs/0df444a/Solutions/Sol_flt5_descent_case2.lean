-- Prove2me | solution 1 for flt5_descent_case2
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T11:12:56.149432+00:00
-- url     : https://prove2.me/submissions/56f47825-4de2-46bc-a1e8-9d84b0c97861
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_descent_step
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.GCD

-- Full descent proof via Nat.strongRecOn + flt5_descent_step
-- The key child theorem flt5_descent_step handles all the algebraic number theory:
--   from (a,b,c) satisfying our conditions, produce (a',b',c') with same conditions and |c'| < |c|
-- This is Dirichlet's 1825 descent argument.

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) : False := by
  suffices key : ∀ n : ℕ, ∀ a b c : ℤ, a ^ 5 + b ^ 5 = c ^ 5 →
      Int.gcd a b = 1 → (5 : ℤ) ∣ c → c ≠ 0 → c.natAbs = n → False from
    key c.natAbs a b c h_eq h_cop h5c hc rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a b c heq hcop h5c hc hcn
    obtain ⟨a', b', c', heq', hcop', h5c', hc', hlt⟩ :=
      flt5_descent_step a b c heq hcop h5c hc
    exact ih c'.natAbs (hcn ▸ hlt) a' b' c' heq' hcop' h5c' hc' rfl
