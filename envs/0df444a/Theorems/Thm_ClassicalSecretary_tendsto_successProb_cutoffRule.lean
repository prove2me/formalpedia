-- Prove2me | Theorems.Thm_ClassicalSecretary_tendsto_successProb_cutoffRule
-- name    : ClassicalSecretary.tendsto_successProb_cutoffRule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T12:52:50.538395+00:00
-- url     : https://prove2.me/theorems/a6f616d4-f452-40f4-b2de-017d467dcf03
-- title:
--   Integral approximation: $P_n(r_n) \to -x\log x$ when $r_n/n \to x$
-- statement:
--   Let $(r_n)$ be cutoffs with $1 \le r_n \le n$ for all large $n$, and suppose $r_n/n \to x$ for some $x \in [0,1]$. Then
--   $$\lim_{n\to\infty} P_n(\text{cutoff } r_n) = x\int_x^1\frac{dt}{t} = -x\log x,$$
--   where the right-hand side is read as $0$ at $x = 0$.
--
--   This is the passage from the exact finite formula to its continuous limit.
--
--   **Formalization Note** The limit is written as `-x * Real.log x`. Since `Real.log 0 = 0`, this equals $0$ at $x=0$, which is the correct limit there.
-- source:
--   Wikipedia, "Secretary problem", https://en.wikipedia.org/wiki/Secretary_problem, section "Deriving the optimal policy", paragraph "Letting n tend to infinity, writing x as the limit of (r−1)/n ... the sum can be approximated by the integral P(x) = x∫_x^1 (1/t) dt = −x ln(x)".

import Mathlib
import Definitions.Def_ClassicalSecretary_Model

open Finset Filter Topology

namespace ClassicalSecretary

theorem tendsto_successProb_cutoffRule (r : ℕ → ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hr : ∀ᶠ n in atTop, 1 ≤ r n ∧ r n ≤ n)
    (hlim : Tendsto (fun n : ℕ => (r n : ℝ) / (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ => successProb n (cutoffRule (r n))) atTop
      (𝓝 (-x * Real.log x)) := by sorry

end ClassicalSecretary
