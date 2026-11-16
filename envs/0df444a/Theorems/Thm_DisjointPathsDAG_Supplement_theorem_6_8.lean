-- Prove2me | Theorems.Thm_DisjointPathsDAG_Supplement_theorem_6_8
-- name    : DisjointPathsDAG.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:02:23.773832+00:00
-- url     : https://prove2.me/theorems/c7e101b3-5319-46df-9f8e-30f85fb8c1d6
-- title:
--   Theorem 6.8 — directed two disjoint shortest paths in expected $O(\min\{mn,n^{\omega+\varepsilon}\})$ time (corrected: an added $m$ term for parallel edges)
-- statement:
--   Let $\omega$ be the exponent of matrix multiplication by bilinear algorithms over $\mathbb F_2$. Let $G$ be a directed graph with $n$ vertices, $m$ edges (parallel edges and self-loops allowed), real edge weights, and two terminal pairs $(s_1,t_1)$, $(s_2,t_2)$ whose four terminals are pairwise distinct. Suppose every directed cycle of $G$ has positive total weight (negative edge weights are otherwise allowed). Put
--   $$T=C\left(m+\min\{mn,\;n^{\omega+\varepsilon}\}+1\right).$$
--   For every $\varepsilon>0$ there is a constant $C$ such that for every $c>0$ there are randomized algorithms on the word RAM of Section 2.1 ($\Theta(\log(m+n))$-bit words, exact real additions and comparisons, a field $\mathbb F_{2^q}$ with $q=O(\log(m+n))$) with:
--
--   1. **Reporting.** Expected running time at most $T$ and at most $T$ storage cells on every run; the algorithm never returns an invalid pair, returns "no" on every infeasible instance, and reports two vertex-disjoint shortest paths with probability at least $1-(m+n)^{-c}$ on every feasible instance.
--   2. **Decision.** Expected running time at most $T$; the answer is never "yes" on an infeasible instance and is "yes" with probability at least $1-(m+n)^{-c}$ on a feasible one.
--
--   This is the directed two disjoint shortest paths theorem (formal version of Theorem 1.3). On graphs without parallel edges $m\le n^2\le n^{\omega+\varepsilon}$ and $m\le mn$, so $T=O(\min\{mn,n^{\omega+\varepsilon}\})$ there; the $m$ term only matters for multigraphs, which must be read in full, and the $+1$ only affects edgeless graphs.
--
--   **Formalization Note** The machine and the input/output layout are those of the base mission (weights in the real bank). $\omega$ is `MME.matMulExp (ZMod 2)`, powers are `Real.rpow`. The word width is $A\lceil\log_2(n+m+2)\rceil$ and the field is $\mathbb F_{2^{q(n+m)}}$ with $q(N)\le A\lceil\log_2(N+2)\rceil$.
--
--   Differences from the source:
--   - correction: expected $O(\min\{mn,n^{\omega+\varepsilon}\})$ time and storage on every directed graph, parallel edges allowed (the proof merges them, p.34) → bound $C(m+\min\{mn,n^{\omega+\varepsilon}\}+1)$ on every directed multigraph; reason: counterexample to the multigraph reading: $n=4$, terminals $s_1=0,t_1=1,s_2=2,t_2=3$, one edge $2\to3$ and $m-1$ parallel edges $0\to1$, all of weight 1; a run that reads fewer than $m-2$ weights leaves some copy other than its output unread, and lowering that weight to 0 makes the same run output an invalid pair; so a never-invalid algorithm needs $\ge m-2$ steps on every successful run, while $\min\{mn,n^{\omega+\varepsilon}\}\le 4^{3+\varepsilon}$ stays bounded. The proof itself first merges parallel edges in $O(m_0+n_0)$ time (p.34, p.43), so the input-reading term $m$ is what is missing; without parallel edges $m\le n^2\le n^{\omega+\varepsilon}$ and $m\le mn$, so the corrected bound is the printed one there
--   - reading: "for every constant c > 0 and every fixed ε > 0, there is a randomized algorithm using expected O(min{mn, nω+ε}) time" → $\varepsilon$ first, then one constant $C$ serving every $c>0$, then the programs, $A$ and $q$; reason: the stronger reading, as in the base goal
--   - reading: "using expected O(min{mn, nω+ε}) time and O(min{mn, nω+ε}) storage cells" → expected running time at most $T$ and at most $T$ storage cells on every tape; reason: the stronger worst-case reading for storage; the proof's storage bound is the deterministic size of the largest live circuit (Lemma 6.7, p.43)
--   - reading: "Evaluating only the root circuit decides feasibility within the same time bound" → a second program with expected running time at most $T$, never 'yes' on an infeasible instance, 'yes' with probability at least $1-(m+n)^{-c}$ on a feasible one (`DecidesExpWithin`); reason: the bound of Theorem 6.8 is an expected one (Lemma 6.1 is Las Vegas), so the decision bound is expected, with the same one-sided error
--   - reading: $\Theta(\log(m+n))$-bit words and $\mathbb F_{2^q}$ with $q=\Theta(\log(m+n))$ → existential $A\ge1$ and $q$ with word width `wordWidth A (n + m)` and $q(N)\le A\lceil\log_2(N+2)\rceil$; reason: upper bounds only, as in the base goal
--   - encoding: $O(m+\min\{mn,n^{\omega+\varepsilon}\})$ → $T=C\,(m+\min\{mn,n^{\omega+\varepsilon}\}+1)$; reason: the $+1$ only matters at $m=0$, where the bound is $0$ and no run takes zero steps; for $m\ge1$ the minimum is at least $4$ ($n\ge4$ terminals, $\omega\ge2$), so $C(x+1)\le\tfrac54Cx$
--   - encoding: every directed cycle has positive total weight → every closed walk of positive length has positive weight (`PositiveCycles`); reason: equivalent: a closed walk splits into directed cycles
--   - encoding: the model of Section 2, $\omega$, four distinct terminals, powers, 'storage cells' → `DisjointPathsDAG.Machine` with `encodeDSP`, `MME.matMulExp (ZMod 2)`, `[s₁, t₁, s₂, t₂].Nodup`, `Real.rpow`, `spaceUsed`; reason: Lean conventions, as in the base goal; same instances
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 6.8, p.43 (formal version of Theorem 1.3, p.3); Lemma 6.1, p.34; Section 2.1, p.6

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_mme_omega
import Definitions.Def_DisjointPathsDAG_Supplement_Guarantees
import Definitions.Def_DisjointPathsDAG_Supplement_PositiveCycles

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG.Supplement

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 6.8 (Directed 2-DSP, formal version of
Theorem 1.3), p.43: "Let G be a directed graph with n vertices, m edges, four distinct terminals, and
real edge weights. Suppose every directed cycle has positive total weight. In the computational model
of Section 2, for every constant c > 0 and every fixed ε > 0, there is a randomized algorithm using
expected O(min{mn, nω+ε}) time and O(min{mn, nω+ε}) storage cells that never returns an invalid pair,
returns no on every infeasible instance, and reports two vertex-disjoint shortest paths with
probability at least 1−(m+n)−c on every feasible instance. Evaluating only the root circuit decides
feasibility within the same time bound."

With `ω = MME.matMulExp (ZMod 2)` and `T := C · (m + min{m n, n^(ω+ε)} + 1)`: for every `ε > 0` there is a
constant `C > 0` such that for every `c > 0` there are a word-width constant `A ≥ 1`, a field-size
function `q` with `q(N) ≤ A · ⌈log₂(N + 2)⌉`, and two programs such that, on every directed graph with
`n` vertices, `m` edges (parallel edges allowed), real edge weights in which every directed cycle (every closed
walk of positive length) has positive weight, and terminal pairs `(s₁, t₁)`, `(s₂, t₂)` with
`s₁, t₁, s₂, t₂` pairwise distinct, run with words of `A · ⌈log₂(n + m + 2)⌉` bits and the field
`F_{2^{q(n+m)}}`:
1. the reporting program has expected running time at most `T`, uses at most `T` storage cells on every
   tape, never outputs an invalid pair, outputs "no" on every infeasible instance, and outputs two
   vertex-disjoint shortest paths with probability at least `1 − (m + n)^(−c)` on every feasible one;
2. the decision program has expected running time at most `T`, never answers "yes" on an infeasible
   instance, and answers "yes" with probability at least `1 − (m + n)^(−c)` on a feasible one.

**Formalization Note** The machine and layouts are those of `DisjointPathsDAG.Machine` and
`DisjointPathsDAG.Encoding` (weights in the real bank). Parallel edges and self-loops are allowed, as
in the paper's preprocessing (p.34: "keep one minimum-weight copy of every set of parallel edges").
Correction: the term `m` is added to the printed bound, since with unboundedly many parallel copies no
algorithm can stay within `O(min{mn, n^(ω+ε)})` (it must read every copy); without parallel edges
`m ≤ n² ≤ n^(ω+ε)` and `m ≤ mn`, so the added term changes nothing there. The `+ 1` only matters at
`m = 0`, where the bound is `0` and no run takes zero steps. `ε` comes before `C`, `C` before
`c`; the programs, `A` and `q` are uniform in `n`, `m` and the instance. Powers are `Real.rpow`. -/
theorem theorem_6_8 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (A : ℕ) (q : ℕ → ℕ) (Prep Pdec : Program), 1 ≤ A ∧
        (∀ N : ℕ, q N ≤ A * Nat.clog 2 (N + 2)) ∧
        ∀ (n m : ℕ) (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin 2 → Fin n × Fin n),
          PositiveCycles G wt →
          [(pairs 0).1, (pairs 0).2, (pairs 1).1, (pairs 1).2].Nodup →
          ReportsWithin 2 Prep (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs)
            (C * ((m : ℝ) + min ((m : ℝ) * n) ((n : ℝ) ^ (MME.matMulExp (ZMod 2) + ε)) + 1))
            (liftSol (IsDSPSolution G wt pairs)) (DSPFeasible G wt pairs)
            (1 - ((m : ℝ) + n) ^ (-c)) ∧
          (∀ ω : Tape (GaloisField 2 (q (n + m))),
            (spaceUsed (wordWidth A (n + m)) (GaloisField 2 (q (n + m))) Prep
              (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs) ω : ℝ≥0∞) ≤
              ENNReal.ofReal
                (C * ((m : ℝ) + min ((m : ℝ) * n) ((n : ℝ) ^ (MME.matMulExp (ZMod 2) + ε)) + 1))) ∧
          DecidesExpWithin Pdec (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs)
            (C * ((m : ℝ) + min ((m : ℝ) * n) ((n : ℝ) ^ (MME.matMulExp (ZMod 2) + ε)) + 1))
            (DSPFeasible G wt pairs) (1 - ((m : ℝ) + n) ^ (-c)) := by sorry

end DisjointPathsDAG.Supplement
