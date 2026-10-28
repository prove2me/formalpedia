-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_downcrossing_implies_compensated_exponential_sup_threshold
-- name    : AvramDividend.Classical.finite_grid_downcrossing_implies_compensated_exponential_sup_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:46:08.205756+00:00
-- url     : https://prove2.me/theorems/35d89e94-1255-4872-9ab1-becb488fe6a4
-- title:
--   A downward crossing at any sampled time forces a compensated exponential maximum past its threshold
-- statement:
--   Let ε>0 and κ≥0, g(k)≥0 be nonnegative sample times, and y(k) arbitrary real sampled states. If there is k≤n with y(k)≤−b, then exp(εb)≤max_{0≤i≤n} exp(−εy(i)+κg(i)). This elementary deterministic inequality translates a sampled lower Lévy-barrier crossing into the maximum event controlled by Doob's compensated Esscher martingale inequality. No probability theory is needed.
-- source:
--   Multiply the downcrossing inequality y(k)≤−b by ε>0; the compensation κg(k)≥0 only increases the exponential threshold. Use monotonicity of Real.exp and the Finset supremum bound at an element of Finset.range(n+1), from k≤n.

import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.finite_grid_downcrossing_implies_compensated_exponential_sup_threshold
    (g : ℕ → NNReal) (y : ℕ → ℝ)
    (ε κ b : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (n k : ℕ) (hk : k ≤ n) (hdown : y k ≤ -b) :
    Real.exp (ε * b) ≤
      (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
        (fun i => Real.exp (-ε * y i + κ * (g i : ℝ))) := by sorry
