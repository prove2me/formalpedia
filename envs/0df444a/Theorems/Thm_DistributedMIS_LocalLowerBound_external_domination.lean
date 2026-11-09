-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_external_domination
-- name    : DistributedMIS.LocalLowerBound.external_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:22.637634+00:00
-- url     : https://prove2.me/theorems/f4921fbc-d9be-4f6c-9233-15e6c47170d7
-- title:
--   Lemma A.4 — External domination
-- statement:
--   Let H be a finite simple D-regular skeleton, with k≥1 coordinates per clique, and pad to n≥kN vertices. For a fixed clique v, let E_v be the event that some choice of at most one vertex from each neighboring clique dominates all k vertices of v. Then
--
--   $$\Pr[E_v]\le\gamma_{EXT}=(k+1)^D\exp(-k2^{-D}).$$
--
--   Outside E_v every maximal independent set of the padded graph occupies v. The choices in E_v are allowed to depend on all matrices; there is no independence assumption on the chosen set.
--
--   Differences from the source:
--   - encoding: N named skeleton vertices, k named clique coordinates, isolated padding to n, and positive graph size → Fin N, Fin k, their disjoint sum with Fin (n-kN), and n≥1; reason: cardinality is exactly n under kN≤n; positivity excludes the undefined log₂ n convention, and legal identifiers are bijections to Fin n read as 1 through n
--   - encoding: finite conditional probabilities of independent fair edge matrices → exact uniform cylinder sums with transposed reverse orientations; reason: only the finitely many required edge variables are averaged; this is the marginal of the infinite fair product law, with arbitrary finite radius retained
--   - generalization: the full numerical regime of Proposition 3.1 → all finite D-regular skeletons and k≥1; reason: the row-independence union bound and maximality implication need neither large degree nor girth; every source instance is included
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.4, printed/PDF pp. 34

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem external_domination (n D k N : ℕ) (hk : 1 ≤ k) (hcap : k*N ≤ n)
    (H : SimpleGraph (Fin N))
    (hreg : ∀ v, by classical exact H.degree v = D) (v : Fin N) :
    matrixProbability {ω : Matrices k | ExternalDomination H v ω} ≤ externalError D k ∧
    ∀ ω : Matrices k, ¬ ExternalDomination H v ω →
      ∀ out : PaddedVertices n N k → Bool, IsMIS (paddedGraph H ω) out →
        ∃ a : Fin k, out (Sum.inl (v,a)) = true := by sorry

end DistributedMIS.LocalLowerBound
