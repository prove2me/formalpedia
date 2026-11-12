-- Prove2me | Theorems.Thm_EuclidCVRP_Main_lemma_5
-- name    : EuclidCVRP.Main.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:40.917225+00:00
-- url     : https://prove2.me/theorems/8fc67fdb-e651-43b3-88b6-10ea8d956395
-- title:
--   Lemma 5 — tour partitioning [HR85; AG87]
-- statement:
--   Let $\gamma\in(0,1]$.
--
--   1. Let $X$ be any metric space with a depot $r$, clients with locations $x_v$, a capacity $Q\ge1$ and demands $0\le d(v)\le Q$. Let $V'$ be a set of clients and $P$ a closed walk through $r$ and the locations of the clients of $V'$, with $\max_{v\in V'}d(v)\le\gamma Q$. Then there is a collection $\mathcal T$ of tours visiting exactly the clients of $V'$, each once, such that $d(V(T))\le\gamma Q$ for every $T\in\mathcal T$ and
--   $$c(\mathcal T)\le c(P)+4\sum_{v\in V'}c(r,v)\,\frac{d(v)}{\gamma Q}.$$
--   2. Such a collection can be computed in polynomial time: a polynomial-time machine reads a rational Euclidean instance, a rational $\gamma\in(0,1]$, the set $V'$ and the rational vertices of $P$, and outputs tours with the two properties above.
--
--   This is the tour-partitioning heuristic of Haimovich–Rinnooy Kan and Altinkemer–Gavish for general demands; in this mission it turns the walk of Lemma 9 into tours (proof of Lemma 6).
--
--   Differences from the source:
--   - generalization: a CVRP instance (V ∪ {r}, c, d, Q) in an arbitrary metric, P a closed walk on its nodes → any metric space X, P a closed walk through arbitrary points of X; reason: the graph metric on V ∪ {r} is the special case X = V ∪ {r}; it also covers the Euclidean walks with Steiner points of Lemma 6
--   - reading: a set 𝒯 of tours visiting all clients in V′ → tours visiting exactly the clients of V′, each once; reason: the tours of the heuristic are the pieces of P restricted to V′, which is how Lemma 6 uses them
--   - reading: we can efficiently compute (arbitrary metric) → a polynomial-time machine (model of Theorem 1) for rational Euclidean instances, rational γ and a walk given by its rational vertices; reason: computation needs a finite input representation; real distances cannot be input, and the mission's instances are rational Euclidean
--   - encoding: a set 𝒯 of tours → a list of tours; reason: no repeated tours arise; cost is the sum
-- source:
--   Jannis Blauth, Fabrizio Grandoni, Bence Mátravölgyi, Ramin Mousavi, Kinter Ren, Mohammad R. Salavatipour, STOC 2027 submission #1236 (October 2026), p. 6, Lemma 5 ([HR85; AG87]), §1.3 Preliminaries

import Mathlib
import Definitions.Def_EuclidCVRP_Main_Machine

set_option autoImplicit false

namespace EuclidCVRP.Main

/-- **Lemma 5** ([HR85; AG87], p. 6), tour partitioning.
(1) For every metric space, every instance (depot `r`, client locations, demands `d(v) ≤ Q`), every
`γ ∈ (0, 1]`, every set `V'` of clients and every closed walk `P` through `r` and the clients of `V'`
with `max_{v ∈ V'} d(v) ≤ γQ`, there are tours visiting exactly the clients of `V'` (each once), each
of demand at most `γQ`, of total cost at most `c(P) + 4 ∑_{v ∈ V'} c(r,v) d(v)/(γQ)`.
(2) Such tours are computable in polynomial time for rational Euclidean instances, rational `γ` and a
walk given by its rational vertices. -/
theorem lemma_5 :
    (∀ (X : Type) [MetricSpace X] (n : ℕ) (r : X) (loc : Fin n → X) (dem : Fin n → ℕ) (Q : ℕ),
      1 ≤ Q → (∀ v, dem v ≤ Q) →
      ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      ∀ (V' : Finset (Fin n)) (P : List X), r ∈ P → (∀ v ∈ V', loc v ∈ P) →
        (∀ v ∈ V', (dem v : ℝ) ≤ γ * Q) →
        ∃ 𝒯 : List (List (Fin n)),
          (∀ v ∈ V', 𝒯.flatten.count v = 1) ∧ (∀ v, v ∉ V' → v ∉ 𝒯.flatten) ∧
          (∀ T ∈ 𝒯, ((∑ v ∈ T.toFinset, dem v : ℕ) : ℝ) ≤ γ * Q) ∧
          (𝒯.map (fun T => closedLen (r :: T.map loc))).sum ≤
            closedLen P + 4 * ∑ v ∈ V', dist r (loc v) * (dem v : ℝ) / (γ * Q)) ∧
    (∃ alg : List Bool → List (List ℕ), PolyTimeFn solBits alg ∧
      ∀ (J : RatInstance) (γ : ℚ) (V' : Finset (Fin J.n)) (P : List (ℚ × ℚ)),
        J.Valid → 0 < γ → γ ≤ 1 → J.depot ∈ P → (∀ v ∈ V', J.loc v ∈ P) →
        (∀ v ∈ V', (J.dem v : ℝ) ≤ (γ : ℝ) * J.Q) →
        ∃ 𝒯 : List (List (Fin J.toInstance.n)),
          J.toInstance.rawSol 𝒯 =
            alg (encInst J ++ ratBits γ ++ listBits natBits ((V'.sort (· ≤ ·)).map Fin.val) ++
              listBits ptBits P) ∧
          (∀ v ∈ V', 𝒯.flatten.count v = 1) ∧ (∀ v, v ∉ V' → v ∉ 𝒯.flatten) ∧
          (∀ T ∈ 𝒯, (J.toInstance.tourDem T : ℝ) ≤ (γ : ℝ) * J.Q) ∧
          J.toInstance.cost 𝒯 ≤ closedLen (P.map toPt) +
            4 * ∑ v ∈ V', dist (toPt J.depot) (toPt (J.loc v)) * (J.dem v : ℝ) / ((γ : ℝ) * J.Q)) := by sorry

end EuclidCVRP.Main
