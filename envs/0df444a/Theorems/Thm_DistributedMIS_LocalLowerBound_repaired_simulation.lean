-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_repaired_simulation
-- name    : DistributedMIS.LocalLowerBound.repaired_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:25.122392+00:00
-- url     : https://prove2.me/theorems/76a6b2ea-ad5f-4a9d-a7e9-0fcaf4e276bb
-- title:
--   Lemma A.2 — The repaired simulation
-- statement:
--   Under the finite obstruction's hypotheses, fix any LOCAL program and any identifier-indexed table W of infinite private tapes. The computed candidate-gating and repair construction is a symmetric radius-(T+3) edge-input rule on the infinite D-regular tree. It is independent on every matrix realization and has zero conflict. For every fixed clique v of the finite skeleton,
--
--   $$p_v\le\min\{1,5000(T+3)\log D/D\}.$$
--
--   The bound holds for each fixed table, before averaging over tapes. No correctness on repeated identifiers or infinite graphs is assumed.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: the infinite D-regular tree with coordinates [k] and output 0 → a SimpleGraph on ℕ satisfying IsRegularTree, coordinates Fin k, and output Option (Fin k); reason: all countable regular trees are isomorphic; coordinate a is source a+1 and none is source 0; all graph automorphisms act, including rooted branch permutations
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - encoding: arbitrary synchronous LOCAL computation and unbounded messages with independent infinite private tapes → one uniform full-state initialization, transition and output program, with total executions; reason: a state can store the original state, tape, round and port table, so every per-port message can be reconstructed from the full-state broadcast; programs may be chosen separately for each n and may idle until T
--   - encoding: one unspecified sufficiently large absolute D₀ → an existential absolute threshold before D, k, radius and rule; reason: the finitely many thresholds can be unified by their maximum; none depends on the radius or rule
--   - generalization: no explicit global constant input in the simulation lemma → any fixed natural-number advice value; reason: a fixed value is part of the uniform rule and introduces no branch names; zero is the unhinted source instance
--   - generalization: a randomized LOCAL algorithm with the usual measurable execution convention → any total LocalProgram, without a MeasurableProgram hypothesis; reason: each tape table is fixed before the matrix experiment, so the simulation is a function of finitely many matrix bits; measurability in the tape table is unnecessary for this assertion
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.2, printed/PDF pp. 33

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem repaired_simulation : ∃ D₀ : ℕ, 3 ≤ D₀ ∧ ∀ (n D k N T advice : ℕ) (hn : 1 ≤ n)
    (H : SimpleGraph (Fin N)) (hH : finiteParameters n D k N T D₀ H)
    (P : LocalProgram) (W : Fin n → PrivateTape),
    (∀ (G : SimpleGraph ℕ) [G.LocallyFinite], IsRegularTree G D →
      IsRule G k (T+3) (simulationRule G (k := k) P n advice T W) ∧
      (∀ u v, G.Adj u v → conflict G (T+3) (simulationRule G (k := k) P n advice T W) u v = 0) ∧
      (∀ u v ω a b, G.Adj u v → edgeBit ω u v a b = true →
        ¬ (simulationRule G (k := k) P n advice T W u ω (some a) = 1 ∧
           simulationRule G (k := k) P n advice T W v ω (some b) = 1))) ∧
    ∀ v : Fin N, finiteOccupancy k P n advice T H W v ≤
      min 1 (5000 * (T+3) * Real.log D / D) := by sorry

end DistributedMIS.LocalLowerBound
