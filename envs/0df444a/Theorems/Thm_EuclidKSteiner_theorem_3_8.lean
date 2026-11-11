-- Prove2me | Theorems.Thm_EuclidKSteiner_theorem_3_8
-- name    : EuclidKSteiner.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:50.490056+00:00
-- url     : https://prove2.me/theorems/0086378e-b10f-40b3-831f-2b6b48521a7c
-- title:
--   Theorem 3.8 — representative subfamilies of size $2^{O(r\log r)}n^{O(1)}$ in $2^{O(r\log r)}|\mathcal A|n^{O(1)}$ real-RAM time
-- statement:
--   There are a deterministic real-RAM program and a constant $C>0$ with the following property. Let $M$ be a tree on a set $P$ of $n$ vertices with nonnegative edge weights, $\Phi$ its attachment value (3.1), $1\le r\le n$, $0\le p\le r$, and $\mathcal A$ a nonempty family of weighted $p$-element subsets of $P$. Given $M$, $r$, $p$ and $\mathcal A$, the program halts within
--   $$C\cdot2^{C\,r\log_2(r+2)}\cdot|\mathcal A|\cdot(n+2)^C$$
--   steps and outputs at most $C\cdot2^{C\,r\log_2(r+2)}(n+2)^C$ distinct positions of $\mathcal A$ whose pairs form a representative subfamily of $\mathcal A$ with respect to $\Phi$ (Definition 2.1, completed size $r$).
--
--   This is the compression step of the dynamic program; with it the algorithm of Theorem 1.1 stays within $2^{O(k\log k)}n^{O(1)}$ time for arbitrary real edge weights.
--
--   **Formalization Note** The machine is the published real RAM restricted to admissible programs (rational literals, no random draws). $P$ is $\{0,\dots,n-1\}$; $M$ is input as its edge list with weights, $\mathcal A$ as a list of pairs.
--
--   Differences from the source:
--   - reading: constructed deterministically in 2^{O(r log r)}|𝒜|n^{O(1)} time on the real RAM, of size 2^{O(r log r)}n^{O(1)} → an admissible MatMulTimeLP.RealRAM program and C > 0 fixed before the input, halting with t + 1 ≤ C·2^{C·r·log₂(r+2)}·|𝒜|·(n + 2)^C and outputting at most C·2^{C·r·log₂(r+2)}·(n + 2)^C positions; reason: O-notation with constants before the input; r log₂(r+2) replaces r log r, which vanishes at r = 1; +2 keeps the base at least 2; real RAM restricted to rational literals and no draws
--   - encoding: a tree M on a set P of n vertices; a nonempty family 𝒜 of weighted p-element subsets → P = {0, …, n−1} (Fin n), M given by an edge listing with weights, 𝒜 a nonempty list of (duplicate-free list of p elements, weight); the output is a list of distinct positions into 𝒜; reason: a machine statement needs an input and output layout
--   - encoding: representative subfamily (Definition 2.1) → Representative T.Phi T.P r p (famSet 𝒜) (famAt 𝒜 L); reason: the encoding of Definition 2.1 given Â ⊆ 𝒜
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Theorem 3.8, p.12 (PDF p.14); restated p.14 (PDF p.16) and p.20 (PDF p.22); proof pp.20–24 (PDF pp.22–26)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Representative
import Definitions.Def_EuclidKSteiner_Layouts

namespace EuclidKSteiner

/-- **Theorem 3.8 (Combinatorial algorithm for representative families).** Bhore, Kisfaludi-Bak,
Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission
(manuscript sha256 75361687…), Theorem 3.8, p.12 (PDF p.14; restated pp.14, 20; proved pp.20–24):
"Let M be a tree on a set P of n vertices where edges have non-negative weights. Let 1 ≤ r ≤ n and
0 ≤ p ≤ r, and let 𝒜 be a nonempty family of weighted p-element subsets of P. Let Φ be defined as in
(3.1), with respect to M. A representative subfamily of 𝒜 with respect to Φ of size
2^{O(r log r)}n^{O(1)} can be constructed deterministically in 2^{O(r log r)}|𝒜|n^{O(1)} time on the
real RAM."

There are an admissible real-RAM program and `C > 0` such that for every tree `M` on
`P = {0, …, n − 1}` with nonnegative weights, every listing of its edges, all `1 ≤ r ≤ n`,
`0 ≤ p ≤ r`, every nonempty list `𝒜` of pairs (a `p`-element subset of `P`, a real weight) and every
tape, on the layout `repLayout` the run halts at a step `t` with
`t + 1 ≤ C·2^{C·r·log₂(r+2)}·|𝒜|·(n + 2)^C` and outputs `m ≤ C·2^{C·r·log₂(r+2)}·(n + 2)^C` distinct
positions into `𝒜` whose pairs form a representative subfamily of `𝒜` for `Φ` (with respect to `M`),
completed size `r` and set size `p` (Definition 2.1).

**Formalization Note** `r·log₂(r+2)` stands for `r log r` (positive at `r = 1`). The family is a
list, so equal pairs may repeat; the represented family is the set of listed pairs. -/
theorem theorem_3_8 :
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (T : TermTree (Fin n)), T.P = Finset.univ →
      ∀ Ls : List (Fin n × Fin n), IsEdgeListing Ls T.M →
      ∀ (r p : ℕ), 1 ≤ r → r ≤ n → p ≤ r →
      ∀ fam : List (List (Fin n) × ℝ), fam ≠ [] → (∀ a ∈ fam, a.1.Nodup ∧ a.1.length = p) →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
        MatMulTimeLP.HaltsAt A (repLayout T.w Ls r p fam) ω t ∧
        (t : ℝ) + 1 ≤
          C * (2 : ℝ) ^ (C * r * Real.logb 2 ((r : ℝ) + 2)) * fam.length * ((n : ℝ) + 2) ^ C ∧
        ∃ L : List ℕ, OutputIs A (repLayout T.w Ls r p fam) ω t (encodePositions L) ∧
          L.Nodup ∧ (∀ j ∈ L, j < fam.length) ∧
          (L.length : ℝ) ≤ C * (2 : ℝ) ^ (C * r * Real.logb 2 ((r : ℝ) + 2)) * ((n : ℝ) + 2) ^ C ∧
          Representative T.Phi T.P r p (famSet fam) (famAt fam L) := by sorry

end EuclidKSteiner
