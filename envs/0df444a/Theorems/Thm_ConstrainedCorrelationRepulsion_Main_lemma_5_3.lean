-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_5_3
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:44.396678+00:00
-- url     : https://prove2.me/theorems/72d82f8a-08c3-444a-b178-fad28b1a6b9f
-- title:
--   Lemma 5.3 — query order, conditional expectation and all inclusion identities
-- statement:
--   The Figure 5 law has an operational implementation querying only local variables on at most $r$ units. Every updated entry has conditional mean equal to its old value on the specified retained index domain. Averaging size, pivot, stopping time, seeds and final independent draws gives, for all vertices $u,v$,
--
--   $$
--   \Pr[v\in C]=\Pr[B(v)\subseteq C]=\mathbb E z_v=1/Z,\qquad \mathbb E z_{uv}=q^0_{uv}.
--   $$
--
--   For vertices in the same unit, the actual joint probability is exactly $q^0_{uv}=1/Z$. The normalizer satisfies $1\le Z\le n$. Early-return conditional values are unit indicators, not independently redrawn coordinates.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
--   - encoding: real expectations of conditional inclusion values → extended nonnegative sums of conditional inclusion values; reason: reachable inclusion values lie in [0,1] and the sampler has finite support, so these equalities are equivalent to the ordinary real expectations
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 5.3, printed p.25 (PDF p.26)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_5_3 :
  (∃ code : Program, ∃ C : ℕ, 0 < C ∧
    ∀ n (I : Instance n) (U : Units n) (r : ℕ) (y : LocalTable n),
      0 < n → 6 ≤ r → Even r → ResidualUnits I U → BoundedOptimal I U r y → RationalTable y →
      let B := lpBound C n r
      BoundedRun false code (samplerOracle I U y) (levelInitial n r) B ∧
      QueriesBounded code I U y r B ∧
      (machineRun false code (samplerOracle I U y) (levelInitial n r) B).map outputSet = candidateLaw I U y r) ∧
  (∀ n (I : Instance n) (U : Units n) (r : ℕ) (y : LocalTable n),
    0 < n → 6 ≤ r → Even r → ResidualUnits I U → BoundedOptimal I U r y → RationalTable y →
    1 ≤ Z y ∧ Z y ≤ n ∧
    (∀ v, eventProbability (candidateLaw I U y r) (fun C => v ∈ C) = 1 / Z y ∧
      eventProbability (candidateLaw I U y r) (fun C => unitOf U v ⊆ C) = 1 / Z y ∧
      nnExpectation (preDrawLaw I U y r) (fun h => preSingle U h v) = ENNReal.ofReal (1 / Z y)) ∧
    (∀ u v, nnExpectation (preDrawLaw I U y r) (fun h => preJoint U h u v) = ENNReal.ofReal (qTarget U y u v)) ∧
    (∀ u v, unitOf U u = unitOf U v → qActual I U y r u v = qTarget U y u v ∧ qTarget U y u v = 1 / Z y) ∧
    (∀ s a, 0 < y s {unitOf U a} → ((unitOf U a).card : ℝ) < s →
      ∀ j, 1 ≤ j → j ≤ r/2 →
      ∀ h ∈ (seedSteps I U r (initialDraw I U y r s a) (j-1)).support,
      ∀ T, T ⊆ eligible I U a → T.card + 1 + j ≤ r →
        nnExpectation (seedStep I U r j h) (fun hnew => hnew.table T) = ENNReal.ofReal (h.table T))) := by sorry

end ConstrainedCorrelationRepulsion.Main
