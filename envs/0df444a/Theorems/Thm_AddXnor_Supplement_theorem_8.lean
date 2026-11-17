-- Prove2me | Theorems.Thm_AddXnor_Supplement_theorem_8
-- name    : AddXnor.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:34:52.728945+00:00
-- url     : https://prove2.me/theorems/d104e235-366f-406d-99d7-fd3647591cb6
-- title:
--   Theorem 8 — Generic hardness of planted search
-- statement:
--   Let $q\ge3$, $h=\lceil q/2\rceil$, and $\max(q,4)\le T\le2^{m-3}$. In the planted ideal-chain experiment, every randomized adaptive adversary making at most $T$ forward or inverse oracle queries succeeds with probability at most
--   $$
--   \frac{3T}{2^h}+\frac{10T^2}{2^m}+\frac1{2^q}.
--   $$
--   Consequently, there is an absolute constant $c>0$ such that success probability at least $1/2$ requires
--   $$
--   T\ge c\min(2^h,2^{m/2}).
--   $$
--   When $m\ge q$, including the balanced case $m=q+1$, this gives $T=\Omega(2^{q/2})$.
--
--   Differences from the source:
--   - encoding: randomized adversary with oracle access → an arbitrary finite probability law over adaptive oracle trees of depth at most $T$; reason: all query, answer, and output spaces are finite, so this represents the same randomized strategies
--   - encoding: independent uniform permutations and planted values → exact nested finite averages over permutation families, initial states, and planted operator strings; reason: finite-type encoding with the same product distribution
-- source:
--   Wang, Lv, Shen, Zhang, manuscript (sha256 405d6dda…), Theorem 8, p.25 (PDF p.25)

import Mathlib
import Definitions.Def_AddXnor_Supplement_ideal

set_option autoImplicit false

namespace AddXnor.Supplement

/-- **Theorem 8 (Generic hardness of planted search)** (Wang, Lv, Shen, Zhang,
*Add/XNOR Chains*, manuscript, sha256 405d6dda..., Theorem 8, p.25 (PDF p.25)).

The first clause is the explicit success bound for every randomized adaptive adversary with at
most `T` forward/inverse permutation queries.  The remaining clauses state the absolute-constant
square-root consequence, including its `m ≥ q` specialization.  This theorem is only about the
independent ideal-permutation planted experiment encoded by `plantedSuccess`. -/
theorem theorem_8 :
    (∀ (q m T : ℕ), 3 ≤ q → max q 4 ≤ T → T ≤ 2 ^ (m - 3) →
      ∀ (R : Type*) [Fintype R] [Nonempty R] (law : FiniteLaw R)
        (adv : R → BitVec m → BitVec m → OracleTree q m T),
        plantedSuccess law adv ≤
          3 * T / (2 : ℝ) ^ ((q + 1) / 2) +
          10 * T ^ 2 / (2 : ℝ) ^ m + 1 / (2 : ℝ) ^ q) ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ (q m T : ℕ), 3 ≤ q → max q 4 ≤ T → T ≤ 2 ^ (m - 3) →
        ∀ (R : Type*) [Fintype R] [Nonempty R] (law : FiniteLaw R)
          (adv : R → BitVec m → BitVec m → OracleTree q m T),
          1 / 2 ≤ plantedSuccess law adv →
            (T : ℝ) ≥ c * min ((2 : ℝ) ^ ((q + 1) / 2))
              (Real.rpow 2 ((m : ℝ) / 2)) ∧
            (m ≥ q → (T : ℝ) ≥ c * Real.rpow 2 ((q : ℝ) / 2)) := by sorry

end AddXnor.Supplement
