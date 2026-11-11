-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_6_1
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:59.250968+00:00
-- url     : https://prove2.me/theorems/63f117d1-15e2-44e3-96f8-7613365a8d95
-- title:
--   Lemma 6.1 — total-cost radius-one repair with a polynomial implementation
-- statement:
--   For every union of residual units $D$, the specified deterministic radius-one Repulsion has a polynomial-time implementation. It partitions $D$ into nonempty disjoint blocks, preserves whole units, and separates every cannot-link pair. Its total internal disagreement cost satisfies
--
--   $$
--   \mathrm{cost}_{I'[D]}(\operatorname{Repulsion}(D))\le\Phi(D)\le\sum_{uv\in\binom D2\setminus H}\bigl[(1-a_{uv})+a_{uv}b(x_{uv})\bigr].
--   $$
--
--   This bounds the total cost of a repaired candidate and asserts no individual pair cut-probability bound. The distance-one potential and $b(1)=2$ are treated explicitly.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - generalization: the metric derived from the selected bounded-LP optimum → any feasible metric that is zero within units; reason: the radius-one proof uses the metric constraints and residual labels; it does not use LP optimality
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 6.1, equation (36), printed p.31 (PDF p.32)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_6_1 :
  ∃ code : Program, Deterministic code ∧ ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n) (U : Units n) (x : Fin n → Fin n → ℝ) (D : Finset (Fin n)),
      ResidualUnits I U → MetricFeasible I x →
      (∀ u v, unitOf U u = unitOf U v → x u v = 0) → UnitUnion U D →
      let B := polynomialBound C d n
      let P := partitionOfBlocks (repair I x D)
      BoundedRun false code (repairOracle I x D) (initialState n) B ∧
      outputLaw code (repairOracle I x D) (initialState n) B false = PMF.pure P ∧
      (∀ A ∈ repair I x D, A.Nonempty) ∧
      ((repair I x D).toFinset.biUnion id = D) ∧
      (∀ A ∈ repair I x D, ∀ B ∈ repair I x D, A ≠ B → Disjoint A B) ∧
      (∀ u ∈ D, ∀ v ∈ D, unitOf U u = unitOf U v → P u = P v) ∧
      (∀ u ∈ D, ∀ v ∈ D, I.cannotLink.Adj u v → P u ≠ P v) ∧
      internalCost I D P ≤ potentialSum (potentialOne I x) D ∧
      potentialSum (potentialOne I x) D ≤
        pairSum (fun u v => if u ∈ D ∧ v ∈ D ∧ ¬ I.cannotLink.Adj u v then
          (if I.positive.Adj u v then b (x u v) else 1) else 0) := by sorry

end ConstrainedCorrelationRepulsion.Main
