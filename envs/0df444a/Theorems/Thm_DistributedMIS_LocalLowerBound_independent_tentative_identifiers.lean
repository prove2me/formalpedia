-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_independent_tentative_identifiers
-- name    : DistributedMIS.LocalLowerBound.independent_tentative_identifiers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:20.935698+00:00
-- url     : https://prove2.me/theorems/db024a99-d43a-4c9f-98ca-5e9bc8d164fc
-- title:
--   Lemma A.1 — Independent tentative identifiers
-- statement:
--   Under the finite obstruction's graph, capacity and parity hypotheses, the explicit XOR-block construction defines tentative identifiers J_{v,a} in [n]. The IDs are jointly independent and every point has probability at most 2/n. For each fixed clique v,
--
--   $$\Pr[\text{an ID collision in }B^H_{T+2}(v)]\le\delta_{ID}.$$
--
--   The same construction is a symmetric radius-one function on the infinite tree. Independence is among identifiers, not between identifiers and the graph. This gives the exact law needed for legal local completion.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the large absolute occupancy threshold D₀ → D≥3 with the remaining finite parameter hypotheses retained; reason: identifier extraction and collision bounds need no occupancy inequality and hold throughout this larger regime
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.1, printed/PDF pp. 32

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem independent_tentative_identifiers (n D k N T : ℕ) (hn : 1 ≤ n)
    (H : SimpleGraph (Fin N)) (hH : finiteParameters n D k N T 3 H) :
    ProbabilityTheory.iIndepFun
      (fun x : Fin N × Fin k => fun ω : Matrices k =>
        tentativeID n (finiteNeighbors H) Fin.val ω x.1 x.2) (matrixMeasure k) ∧
    (∀ x : Fin N × Fin k, ∀ ω,
      1 ≤ tentativeID n (finiteNeighbors H) Fin.val ω x.1 x.2 ∧
      tentativeID n (finiteNeighbors H) Fin.val ω x.1 x.2 ≤ n) ∧
    (∀ x : Fin N × Fin k, ∀ i : ℕ, matrixProbability
      {ω | tentativeID n (finiteNeighbors H) Fin.val ω x.1 x.2 = i} ≤ 2 / (n : ℝ)) ∧
    (∀ v : Fin N, matrixProbability
      {ω : Matrices k | ¬ distinctIDs n (T+2) (finiteNeighbors H) Fin.val ω v} ≤ identifierError n D k T) ∧
    (∀ (G : SimpleGraph ℕ) [G.LocallyFinite], IsRegularTree G D →
      let J := fun v ω a => tentativeID n (fun u => (G.neighborFinset u).toList) id ω v a
      (∀ v ω ξ, (∀ i ∈ viewBits G k 1 v, ω i = ξ i) → J v ω = J v ξ) ∧
      (∀ e : G ≃g G, ∀ v ω, J (e v) ω = J v (pullMatrices e.toEquiv ω))) := by sorry

end DistributedMIS.LocalLowerBound
