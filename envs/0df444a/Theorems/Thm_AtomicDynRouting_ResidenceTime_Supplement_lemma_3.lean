-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_Supplement_lemma_3
-- name    : AtomicDynRouting.ResidenceTime.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:35:41.275411+00:00
-- url     : https://prove2.me/theorems/791c2f3a-da2e-4013-aea1-fe9289c9a919
-- title:
--   Lemma 3, p. 15 — for subnetworks G1, G2 joined in parallel, the populations at equilibrium satisfy n1 ≤ D(L + n2 + 1)
-- statement:
--   Let $G=(V,E)$ be an $o$-$d$ series-parallel network with a fixed construction, and let $\mathcal S$ be the set of subnetworks appearing in it. Consider an ADR game $\Gamma_1$, $\Gamma_2$ or $\Gamma_3$ on $G$ (unit capacities, finitely many agents entering at each integer time) and an equilibrium $p$: a UFR equilibrium for $\Gamma_1,\Gamma_2$, a Nash equilibrium for $\Gamma_3$. Let $D=\max_{v\in V}|E^-_v|$ be the maximum in-degree of $G$ and $L$ the length of a longest $o$-$d$ path. Suppose $G_1,G_2\in\mathcal S$ are connected in parallel to form a subnetwork in $\mathcal S$, and at some integer time they accommodate $n_1$ and $n_2$ agents respectively (agents in the buffers of their edges). Then
--   $$n_1\le D\,(L+n_2+1).$$
--
--   No bound on the inflow is assumed. The lemma is the population-ratio estimate on which the parallel step (Lemma 5) of the proof of Theorem 4 rests.
--
--   Differences from the source:
--
--   - encoding: the three games of §5.1 with their priority lists → Game with Rule r1/r2/r3; priorities as strict total orders (Γ3: an order of all of E per vertex, one global original order) and the run built by recursion on time; reason: only the restrictions to incoming edges and to each Δ_r are used, and every family of such orders is a restriction; the recursion is the deterministic dynamics the rules determine
--   - encoding: G1, G2 ∈ S connected in parallel, for a fixed sequence of connection operations → a construction tree T of G and G1, G2 the children (in either order) of a parallel node of T; reason: the operation sequences leading to G are exactly the construction trees; the statement holds for every one
--   - encoding: the number of agents G1 accommodates → Game.accommodates p (edges of G1) t, a Set.ncard of agents in the buffers of its edges; reason: the set counted is finite (only agents who have entered by t), so ncard is the count
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 15 (PDF 16), §6.1, Lemma 3 (D, L and accommodation defined on the same page)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_SeriesParallel

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem lemma_3 {ι V E : Type} [Fintype V] [Fintype E] [DecidableEq V] (G : Game ι V E) (hG : G.Standing) (T : SPTree E) (hT : IsSPConstruction G.N G.o G.d T) (G₁ G₂ : SPTree E) (hpar : SPTree.IsNode (.par G₁ G₂) T ∨ SPTree.IsNode (.par G₂ G₁) T) (p : ι → List E) (hp : G.IsEquilibrium p) (t : ℕ) : G.accommodates p G₁.edges t ≤ maxInDeg G.N * (G.N.longest G.o G.d + G.accommodates p G₂.edges t + 1) := by sorry

end AtomicDynRouting.ResidenceTime.Supplement
