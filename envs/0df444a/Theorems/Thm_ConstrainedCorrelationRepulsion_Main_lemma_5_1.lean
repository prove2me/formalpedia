-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_5_1
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:33:17.209763+00:00
-- url     : https://prove2.me/theorems/11b61fec-2f9b-4a7b-9584-952a462c6165
-- title:
--   Lemma 5.1 — rational LP computation, lower bound and size identities
-- statement:
--   For units obtained by preclustering, the bounded LP is feasible and has a rational optimal solution computable by one deterministic program in $n^{O(r)}$ charged work, with polynomial bit length and LP size. Its optimum satisfies $L\le\mathrm{OPT}(I')$. The derived distances are metric-feasible. For every feasible table, $s\in[n]$ and $T\subseteq\mathcal U$ with $|T|\le r-1$, the following identity holds, and $y_{s,T}=0$ whenever $\sum_{B\in T}|B|>s$:
--
--   $$
--   \left(s-\sum_{B\in T}|B|\right)y_{s,T}=\sum_{B\in\mathcal U\setminus T}|B|y_{s,T\cup\{B\}}\ge0.
--   $$
--
--   The program reads only the residual graph, unit partition and level; no solver or optimality guarantee is supplied by the input. Variables and constraints are counted explicitly.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - generalization: the fixed optimal LP table in the surrounding section → the metric consequences and identity (13) for every feasible table with residual unit conditions; reason: their proofs use only constraints (2)–(6); the optimal-value assertion remains for optimal tables
--   - generalization: the preclustering input normalized as stipulated in Section 4 → a Figure 4 trace from any feasible unweighted cannot-link input; reason: the full preclustering guarantees hold without the initial normalization; the residual labels and unit conditions needed in Section 5 are unchanged
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 5.1 and equations (10)–(13), printed pp.22–23 (PDF pp.23–24)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_LPSize

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_5_1 :
  (∃ code : Program, Deterministic code ∧ ∃ C : ℕ, 0 < C ∧
    ∀ n (I J : Instance n) (U : Units n) (r : ℕ),
      FeasibleInput I → I.mustLink = ⊥ → PreclusterTrace I J U → 3 ≤ r →
      let B := lpBound C n r
      lpSize J U r ≤ B ∧
      BoundedRun true code (lpInputOracle J U) (levelInitial n r) B ∧
      ∀ s ∈ (machineRun true code (lpInputOracle J U) (levelInitial n r) B).support,
        let y := readTable U r s
        BoundedOptimal J U r y ∧ RationalTable y ∧ L J U y ≤ (OPT J : ℝ) ∧
        ∀ layer T, realBits (y layer T) ≤ B) ∧
  (∀ n (I : Instance n) (U : Units n) (r : ℕ) (y : LocalTable n),
    3 ≤ r → ResidualUnits I U → BoundedFeasible I U r y →
    MetricFeasible I (tableDistance U y) ∧
    ∀ s ∈ Finset.Icc 1 n, ∀ T, T ⊆ U.blocks → T.card + 1 ≤ r →
      ((s : ℝ) - ∑ B ∈ T, (B.card : ℝ)) * y s T =
        ∑ B ∈ U.blocks \ T, (B.card : ℝ) * y s (insert B T) ∧
      0 ≤ ∑ B ∈ U.blocks \ T, (B.card : ℝ) * y s (insert B T) ∧
      ((s : ℝ) < ∑ B ∈ T, (B.card : ℝ) → y s T = 0)) := by sorry

end ConstrainedCorrelationRepulsion.Main
