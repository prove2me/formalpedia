-- Prove2me | Theorems.Thm_DetCCHard_theorem_A_3
-- name    : DetCCHard.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:38:16.333945+00:00
-- url     : https://prove2.me/theorems/cdb195c1-6764-46ce-a7bb-e23aa1e036e4
-- title:
--   Theorem A.3 — short protocols for a width-$u$ interlace begin with $\log u$ Alice bits that separate the blocks
-- statement:
--   Suppose $\mathcal P(M; \rho, d)$ with $d \ge 2$ and $0 < \rho \le 1$. Let $u = 2^r \ge 2$ and $1 \ge \xi > 2u\rho$. Interlace $M$ at width $u$ on an exactly 8-wise independent tuple list with the base-column marginal. Let a restriction $U \times K$ retain base row weight at least $\xi$ in every block and tuple-label weight at least $18/25$. Then every protocol of depth at most $d + \log u$ that is correct on $U \times K$:
--
--   1. begins with $\log u$ Alice bits along every path, and
--   2. its $u$ nodes at depth $\log u$ are in bijection $\sigma$ with the blocks: each such node $w$ retains more than $\xi - 2(u-1)\rho$ of block $\sigma(w)$ and less than $2\rho$ of every other block.
--
--   Full products are a special case, and fixed bits count as transmitted bits. The theorem is what makes Alice's first $\log s$ bits name a bin in the NO-case lower bound.
--
--   **Formalization Note** A node at depth $\log u$ is a word $w \in \{0,1\}^r$; "begins with $\log u$ Alice bits" means every node at depth $< r$ exists and is an Alice node. The rows retained by node $w$ are the rows of $U$ that produce $w$ through Alice's bits, and the retained part of a block is its base row weight (no division by $u$).
--
--   Differences from the source:
--   - encoding: u ≥ 2 dyadic, log u → u = 2^r with r ≥ 1; reason: same instances
--   - encoding: nodes at depth log u and the rows a node retains → words of length r; the rows of U that produce the word through Alice nodes; reason: for a protocol whose first r levels are Alice nodes these are the paper's nodes and their retained rows
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem A.3, p.51

import Mathlib
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_DeletionBounds
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_interlaceOn

namespace DetCCHard

/-- **Theorem A.3 (separation)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, Theorem A.3, p.51). Suppose `P(M; ρ, d)` with `d ≥ 2`. Let `u = 2^r ≥ 2` and
`1 ≥ ξ > 2uρ`. Interlace `M` at width `u` on an exactly 8-wise independent tuple list with the
base-column marginal. For every restriction `U × K` retaining base row weight at least `ξ` in every
block and tuple-label weight at least `18/25`, every protocol of depth at most `d + log u` that is
correct on `U × K` begins with `log u` Alice bits along every path, and there is a bijection `σ`
between the `u` nodes at depth `log u` and the blocks such that each node `w` retains more than
`ξ − 2(u − 1)ρ` of block `σ(w)` and less than `2ρ` of every other block.

**Formalization Note** A node at depth `r` is the word `w ∈ {0,1}^r` of bits leading to it. "Begins
with `log u` Alice bits along every path" is: every node at depth `< r` exists and is an Alice
node. The rows retained by node `w` are the rows of `U` that produce `w` through Alice's bits
(`aliceReach`), and "retains … of block `i`" is the base row weight `blockWt` of those rows in
block `i` (Definition 4.4, without division by `u`). Blocks are indexed from `0`. The full product
is one exactly 8-wise independent tuple list, so it is covered. `ρ` is real with `0 < ρ ≤ 1`
(Definition 5.1). -/
theorem theorem_A_3 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (μX : X → ℚ)
    (μY : Y → ℚ) (hμX : IsWeight μX) (hμY : IsWeight μY) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (d : ℕ) (hd : 2 ≤ d) (hP : DeletionBounds M μX μY ρ d) (r : ℕ) (hr : 1 ≤ r) (ξ : ℝ)
    (hξ1 : ξ ≤ 1) (hξ : 2 * 2 ^ r * ρ < ξ) (T : TupleList Y (Fin (2 ^ r)))
    (hT : ExactlyIndep T 8 μY) (U : Set (Fin (2 ^ r) × X)) (K : Set T.L)
    (hU : ∀ i, ξ ≤ (blockWt μX U i : ℝ)) (hK : (18 / 25 : ℚ) ≤ wt T.ν K)
    (P : Protocol (Fin (2 ^ r) × X) T.L) (hPd : P.depth ≤ d + r)
    (hPc : ∀ x ∈ U, ∀ y ∈ K, P.eval x y = interlaceOn M T x y) :
    (∀ w : List Bool, w.length < r → IsAliceNode (P.nodeAt w)) ∧
      ∃ σ : {w : List Bool // w.length = r} ≃ Fin (2 ^ r), ∀ w,
        ξ - 2 * (2 ^ r - 1) * ρ < (blockWt μX (U ∩ P.aliceReach w.1) (σ w) : ℝ) ∧
        ∀ i, i ≠ σ w → (blockWt μX (U ∩ P.aliceReach w.1) i : ℝ) < 2 * ρ := by sorry

end DetCCHard
