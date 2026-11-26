-- Prove2me | Theorems.Thm_Erdos287_omission_mass_extends_pair_band
-- name    : Erdos287.omission_mass_extends_pair_band
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T03:12:31.229027+00:00
-- url     : https://prove2.me/theorems/a8faf7cb-9139-5004-9145-a88bd32f9359
-- title:
--   Reciprocal mass of certified omissions extends the pair exclusion interval
-- statement:
--   Let $n_0<\cdots<n_{k-1}=M$ be a strictly increasing list of integers with reciprocal sum one. Fix an integer $x\ge1$ with $x+1\le M$, and let $H\subseteq [x,M]\cap\mathbb Z$ be a set of integers absent from the list that contains both $x$ and $x+1$. If
--
--   $$
--   \log(M/x)<1+\sum_{h\in H\setminus\{x\}}\frac1h,
--   $$
--
--   then some consecutive denominator gap is at least three.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. A harmonic-mass refinement of the range covered by a consecutive pair.

import Mathlib

theorem Erdos287.omission_mass_extends_pair_band (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (x : ℕ) (hx : 0 < x) (hM : x + 1 ≤ f (k - 1))
    (H : Finset ℕ) (hH : ∀ n ∈ H, x ≤ n ∧ n ≤ f (k - 1))
    (hmiss : ∀ i, i < k → f i ∉ H) (hxH : x ∈ H) (hxH' : x + 1 ∈ H)
    (hmass : Real.log ((f (k - 1) : ℝ) / x) < 1 + ∑ n ∈ H.erase x, (1 : ℝ) / n) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
