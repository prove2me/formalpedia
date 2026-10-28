-- Prove2me | Theorems.Thm_EReal_exists_real_gt_of_average_lt
-- name    : EReal.exists_real_gt_of_average_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:28.124496+00:00
-- url     : https://prove2.me/theorems/bd2d7e16-d16b-4694-8e61-676ae4dd30a0
-- title:
--   Real majorants of extended reals whose average stays below a given bound
-- statement:
--   Let $a_0, \dots, a_{N-1}$ be extended real numbers, none of them $+\infty$, and let
--   $r \in \mathbb{R}$ be a bound strictly above their average:
--
--   $$
--   \frac{1}{N} \sum_{i} a_i < r .
--   $$
--
--   Then each $a_i$ can be majorized by a *real* number without losing the bound: there are
--   $s_0, \dots, s_{N-1} \in \mathbb{R}$ with
--
--   $$
--   a_i < s_i \quad \text{for every } i, \qquad \frac{1}{N} \sum_{i} s_i < r .
--   $$
--
--   Replacing extended reals by real numbers one index at a time is easy; doing it while keeping a
--   strict bound on the average is the step that needs care, because the slack has to be divided
--   among the indices and some $a_i$ may be $-\infty$. This is the form in which the passage from
--   an extended-real objective to a real one is used in empirical risk arguments, where the average
--   is the empirical mean over $N$ samples.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 2604-2651, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem EReal.exists_real_gt_of_average_lt {N : ℕ} (a : Fin N → EReal)
    (hne_top : ∀ i, a i ≠ ⊤) (r : ℝ)
    (hr : ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, a i) < (r : EReal)) :
    ∃ s : Fin N → ℝ, (∀ i, a i < (s i : EReal)) ∧ (1/(N : ℝ))*∑ i, s i < r := by sorry
