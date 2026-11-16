-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_9_4
-- name    : DetCCHard.Supplement.theorem_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:00:30.704983+00:00
-- url     : https://prove2.me/theorems/8a093ea0-03bd-4405-816e-d40ed7a02aa0
-- title:
--   Theorem 9.4 — sampling $m$ rows and $m$ columns keeps cost $\ge H$ except with probability $< 1/100$
-- statement:
--   Let $F : X \times Y \to \{0,1\}$ have real rank at most $r$, where $r \ge 1$ is an integer, and let $\mu_X, \mu_Y$ be input distributions on nonempty finite sets. Suppose an integer $H \ge 1$ satisfies, for all $U \subseteq X$ and $V \subseteq Y$,
--   $$
--   \mu_X(U) \ge 3/5,\ \mu_Y(V) \ge 3/5 \implies D(F[U, V]) \ge H .
--   $$
--   Put $m = \mathrm{pow}_2\bigl(16(r+1)\lceil \log(r+2) \rceil 2^H\bigr)$. Draw $m$ rows from $\mu_X$ and $m$ columns from $\mu_Y$, all independently, retaining separate indices for repeated draws. Then the resulting $m \times m$ matrix has cost at least $H$ except with probability less than $1/100$, and on every sample outcome it has cost at most $D(F)$.
--
--   This replaces the iterated matrix, too large to print, by a small sampled table that keeps the NO-case lower bound with high probability.
--
--   **Formalization Note** An outcome is a pair of draws $a : [m] \to X$, $b : [m] \to Y$ with probability $\prod_i \mu_X(a_i) \prod_j \mu_Y(b_j)$; the sampled matrix is $(i, j) \mapsto F(a_i, b_j)$.
--
--   Differences from the source:
--   - generalization: input distributions (the paper's input weights are positive normalized rationals, §4.2) → arbitrary real distributions: nonnegative weights summing to one; reason: positive normalized rational weights are a special case
--   - encoding: drawing with separate indices for repeated draws → outcomes (a, b) ∈ X^m × Y^m with product probability, matrix indexed by draws; reason: the same probability space
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 9.4, pp.39–40

import Mathlib
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_realRank
import Definitions.Def_DetCCHard_pow2

namespace DetCCHard.Supplement

open DetCCHard

open Classical in
/-- **Theorem 9.4 (Sampling rows and columns)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 9.4, pp.39–40). Let
`F : X × Y → {0, 1}` have real rank at most `r`, where `r ≥ 1` is an integer, and let `μX`, `μY` be
input distributions on nonempty finite indexed sets. Suppose an integer `H ≥ 1` satisfies, for all
`U ⊆ X` and `V ⊆ Y`, `μX(U) ≥ 3/5, μY(V) ≥ 3/5 ⟹ D(F[U, V]) ≥ H`. Put
`m = pow2(16(r + 1)⌈log(r + 2)⌉ 2^H)`. Draw `m` rows from `μX` and `m` columns from `μY`, all
independently, retaining separate indices for repeated draws. The resulting `m × m` matrix has cost
at least `H` except with probability less than `1/100`. Every protocol for `F` also computes the
sampled matrix, so the sampled matrix has cost at most `D(F)` on every sample outcome.

**Formalization Note** An outcome is a pair `(a, b)` of row and column draws `a : [m] → X`,
`b : [m] → Y`, of probability `∏ μX(a_i) ∏ μY(b_j)`; the sampled matrix is `(i, j) ↦ F(a_i, b_j)`,
indexed by draws. The input distributions are real, nonnegative and sum to one (so `X`, `Y` are
nonempty). `⌈log(r + 2)⌉ = Nat.clog 2 (r + 2)`; rank is over `ℝ`; `D` is `Dcost`. -/
theorem theorem_9_4 {X Y : Type} [Fintype X] [Fintype Y] (F : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : realRank F ≤ r) (μX : X → ℝ) (μY : Y → ℝ) (hμX0 : ∀ x, 0 ≤ μX x)
    (hμX1 : ∑ x, μX x = 1) (hμY0 : ∀ y, 0 ≤ μY y) (hμY1 : ∑ y, μY y = 1) (H : ℕ) (hH : 1 ≤ H)
    (hF : ∀ (U : Set X) (V : Set Y), (3 / 5 : ℝ) ≤ ∑ x ∈ Finset.univ.filter (· ∈ U), μX x →
      (3 / 5 : ℝ) ≤ ∑ y ∈ Finset.univ.filter (· ∈ V), μY y → H ≤ commCost F U V) :
    let m := pow2 (16 * (r + 1) * Nat.clog 2 (r + 2) * 2 ^ H)
    (∑ ab ∈ Finset.univ.filter (fun ab : (Fin m → X) × (Fin m → Y) =>
        Dcost (fun i j => F (ab.1 i) (ab.2 j)) < H),
        (∏ i, μX (ab.1 i)) * ∏ j, μY (ab.2 j)) < 1 / 100 ∧
      ∀ (a : Fin m → X) (b : Fin m → Y), Dcost (fun i j => F (a i) (b j)) ≤ Dcost F := by sorry

end DetCCHard.Supplement
