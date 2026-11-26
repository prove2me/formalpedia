-- Prove2me | Theorems.Thm_Erdos287_affine_pair_denominator_window
-- name    : Erdos287.affine_pair_denominator_window
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:05:23.686446+00:00
-- url     : https://prove2.me/theorems/d7d6baac-0ff8-4e2a-a6ea-9fb13a7426b3
-- title:
--   Compatible affine pairs in general denominator windows
-- statement:
--   Let $a<b$, with $b-a$ dividing $a$, and put $c=a/(b-a)$. Given positive $M,d,V$, suppose the scale distance $d$, the parameter $Qt$, and the coefficient $cb$ satisfy the displayed lower and upper bounds. If $(37/100)d_(hi)<c_(lo)t_(lo)$, $c_(hi)t_(hi)le(1-epsilon)d_(lo)$, and $c+1le epsilon M$, there is an integer $x>0$ with $bt+1$ dividing $x$, $at+1$ dividing $x+1$, and $x+1le M<ex$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Banks–Freiberg–Maynard, https://arxiv.org/abs/1404.5094. Polymath, https://arxiv.org/abs/1407.4897.

import Mathlib

theorem Erdos287.affine_pair_denominator_window (a b t M : ℕ) (Q d V dLo dHi tLo tHi cLo cHi ε : ℝ)
    (hM : 0 < M) (hab : a < b) (hdiv : (b - a) ∣ a)
    (hd : 0 < d) (hV : 0 < V)
    (hcLo : 0 ≤ cLo) (hcHi : 0 ≤ cHi) (hε : ε ≤ 1)
    (hdlo : dLo * V / M ≤ d) (hdhi : d ≤ dHi * V / M)
    (htlo : tLo * V ≤ Q * t) (hthi : Q * t ≤ tHi * V)
    (hcoeflo : cLo * Q / d ≤ ((a / (b - a) : ℕ) : ℝ) * b)
    (hcoefhi : ((a / (b - a) : ℕ) : ℝ) * b ≤ cHi * Q / d)
    (hWindowLo : (37 / 100 : ℝ) * dHi < cLo * tLo)
    (hWindowHi : cHi * tHi ≤ (1 - ε) * dLo)
    (herror : ((a / (b - a) + 1 : ℕ) : ℝ) ≤ ε * (M : ℝ)) :
    ∃ x : ℕ, 0 < x ∧ (b * t + 1) ∣ x ∧ (a * t + 1) ∣ (x + 1) ∧
      x + 1 ≤ M ∧ (M : ℝ) < Real.exp 1 * x := by sorry
