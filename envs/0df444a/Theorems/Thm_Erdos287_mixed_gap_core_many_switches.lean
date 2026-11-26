-- Prove2me | Theorems.Thm_Erdos287_mixed_gap_core_many_switches
-- name    : Erdos287.mixed_gap_core_many_switches
-- status  : Open
-- author  : @immiq
-- created : 2026-11-26T02:35:17.920445+00:00
-- url     : https://prove2.me/theorems/a44c75c7-e1eb-4d43-97e1-f93f96b61d7c
-- title:
--   Erdős 287 residual: at least eight unit gaps and bounded max for a fixed gap count
-- statement:
--   This is the remaining case of Erdős Problem 287 after excluding small numbers of unit gaps. Let $1<n_0<dots<n_{k-1}=M$ be integers whose reciprocals sum to one, with all consecutive gaps at most two. Put $t=\#\{i:n_{i+1}-n_i=1\}$ and $B=4(t+3)$. Show that the following conditions are impossible together:
--   $$
--   t\ge 8\,,\qquad M<B\bigl(B\operatorname{lcm}(1,\ldots,B)+1\bigr).
--   $$
--   Both conditions follow from the verified gap-count bounds. This is an open mathematical statement.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Remaining case of https://prove2.me/theorems/14ba1360-7f80-408d-96bf-de1f2fca500d using the proved gap-count restrictions.

import Mathlib

theorem Erdos287.mixed_gap_core_many_switches (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hcount : 8 ≤ ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card)
    (hM : let t := ((Finset.range (k - 1)).filter (fun i => f (i + 1) - f i = 1)).card
          let B := 4 * (t + 3)
          f (k - 1) < B * (B * Nat.lcmUpto B + 1)) : False := by sorry
