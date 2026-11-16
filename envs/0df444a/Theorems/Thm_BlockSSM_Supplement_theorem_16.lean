-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_16
-- name    : BlockSSM.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:08:27.692646+00:00
-- url     : https://prove2.me/theorems/49eb4d5a-afe0-4166-a1a1-9f6d6726734b
-- title:
--   Theorem 16 — exact cascade depth $\ell_b(G)$
-- statement:
--   Let $G$ be a finite group and $b$ a block bound.
--   1. The least depth of a finite-state cascade with blocks of size at most $b$ that tracks $G$ equals $\ell_b(G)$, the least length $k$ of a subnormal series $1=N_0\trianglelefteq\dots\trianglelefteq N_k=G$ with every factor $N_i/N_{i-1}$ in $V_b$ (and $\infty$ if none exists).
--   2. The minimum is unchanged if every $N_i$ is required to be normal in $G$.
--   3. For every such series of length $k$ there is a finite-state depth-$k$ cascade with blocks of size at most $b$ that tracks $G$ and has total hidden dimension
--   $$
--   \sum_{i=1}^kD_b(N_i/N_{i-1}).
--   $$
--
--   The sum is an upper bound, not a claimed optimum for total dimension. The theorem identifies the depth needed by stacked block-diagonal recurrences with a composition-type invariant of the group.
--
--   Differences from the source:
--   - generalization: an integer block bound $b$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`), every value including $b=\infty$; reason: every integer bound is a case through the cast and $b=\infty$ is the unbounded case ($D_\infty$ of Definition 2); the argument is the same
--   - reading: "for any such series" → every subnormal series with factors in $V_b$; reason: the antecedent may be the normal series of the previous sentence or the subnormal series defining $\ell_b$; the subnormal reading contains the normal one
--   - encoding: a depth-$k$ cascade with alphabets $\Sigma_j$, $\Sigma_1=G$, interfaces $\psi_j(h^j_t,u^j_t)$ and a decoder on the full stack → the inductive `Cascade b G k`, with tracking as the existence of a decoder on the stack state; reason: the same model; the first layer reads the input alphabet $G$ directly
--   - encoding: a minimum with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 16, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_BlockSSM_Supplement_Cascade
import Definitions.Def_BlockSSM_Supplement_VbSeries

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 16 (cascade depth).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 16, p.8 (PDF p.9): "The least finite-state
cascade depth at block size at most b that tracks G is ℓ_b(G). The minimum is unchanged if every
N_i is required to be normal in G. For any such series, a cascade exists with total dimension
∑_{i=1}^k D_b(N_i/N_{i−1}). This sum is an upper bound, not a claimed general optimum for total
dimension."

Three conclusions: (1) `cascadeDepth G b = ℓ_b(G)`; (2) the least length of a series with factors in
`V_b` whose terms are all normal in `G` is also `ℓ_b(G)`; (3) for every subnormal series
`1 = N₀ ⊴ ⋯ ⊴ N_k = G` with factors in `V_b` there is a depth-`k` finite-state cascade with blocks at
most `b` that tracks `G` and has total hidden dimension exactly `∑_{i=1}^k D_b(N_i/N_{i−1})`.

**Formalization Note.** The cascade model is `Cascade` (§8: layers of §2 over finite alphabets,
interface `ψ_j(h^j_t, u^j_t)` reading the updated state, one decoder on the full stack). "Such
series" in (3) is read as any subnormal series with factors in `V_b`, which includes the normal
ones. Values in `ℕ∞`. -/
theorem theorem_16 (G : Type u) [Group G] [Finite G] (b : ℕ∞) :
    cascadeDepth G b = seriesLength G b ∧ normalSeriesLength G b = seriesLength G b ∧
      ∀ (k : ℕ) (S : VbSeries G b k), ∃ C : Cascade b G k, C.Tracks ∧ C.IsFiniteState ∧
        (C.totalDim : ℕ∞) = ∑ i : Fin k, haveI := S.normal i;
          coverDim (↥(S.N i.succ) ⧸ (S.N i.castSucc).subgroupOf (S.N i.succ)) b := by sorry

end BlockSSM.Supplement
