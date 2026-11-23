-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_Supplement_theorem_4
-- name    : AtomicDynRouting.ResidenceTime.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:36:18.778747+00:00
-- url     : https://prove2.me/theorems/b15f720f-eb21-4990-b685-048a721a0be2
-- title:
--   Theorem 4, p. 20 — at equilibrium on a series-parallel network with m edges, at most (12m)^m agents are inside at any time (standing assumption (6.1) includes t = 0)
-- statement:
--   Let $G$ be an $o$-$d$ series-parallel network with $m$ edges and capacity $|\Xi(G)|$ (the minimum number of edges of an $o$-$d$ cut). Consider an ADR game $\Gamma_1$, $\Gamma_2$ or $\Gamma_3$ on $G$ in which, at every integer time $t\ge0$, at most $|\Xi(G)|$ agents enter:
--   $$|\Delta_t|\le|\Xi(G)|\qquad\text{for all }t\ge0.$$
--   Then for every UFR equilibrium of $\Gamma_1$ or $\Gamma_2$, and every Nash equilibrium of $\Gamma_3$, the number of agents inside $G$ at any integer time is at most
--   $$(12m)^m.$$
--
--   This answers the equilibrium queue length problem (EQLP) on series-parallel networks: if the inflow never exceeds the capacity, queues stay bounded by a constant depending only on the network.
--
--   **Formalization Note** The theorem sentence repeats the inflow bound for $t\ge1$. The opening of §6.2 (p. 19, PDF 20) explicitly assumes (6.1), the bound at each integer time point, for the entire subsection. Time starts at $0$, and the proof of Theorem 4 invokes (6.1). The Lean makes this governing assumption explicit for every $t\ge0$; it excludes no case allowed by the full source context.
--
--   Differences from the source:
--
--   - reading: the theorem sentence says t ≥ 1; §6.2 assumes (6.1) at each integer time point throughout the subsection → hin bounds |Δ_t| by the minimum cut size for every t : ℕ, including 0; reason: the Lean includes the governing section assumption explicitly; time starts at 0 (§2.2), and the proof invokes (6.1); the isolated-sentence counterexample violates this standing assumption
--   - encoding: the three games of §5.1 with their priority lists → Game with Rule r1/r2/r3; priorities as strict total orders (Γ3: an order of all of E per vertex, one global original order) and the run built by recursion on time; reason: only the restrictions to incoming edges and to each Δ_r are used, and every family of such orders is a restriction; the recursion is the deterministic dynamics the rules determine
--   - encoding: 'upper bounded by a constant at most (12m)^m' → Game.population p t ≤ (12 m)^m for every t, m = Fintype.card E; reason: a bound by a constant at most (12m)^m is the bound (12m)^m
--   - encoding: |Ξ(G)|, the size of the leftmost minimum cut → minCut: the minimum number of edges of an o-d cut; reason: all minimum cuts have the same size; only the size enters the statement
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 20 (PDF 21), Theorem 4 and its proof; (6.1) p. 19 (PDF 20); capacity p. 15 (PDF 16)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_SeriesParallel

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem theorem_4 {ι V E : Type} [Fintype V] [Fintype E] (G : Game ι V E) (hG : G.Standing) (hSP : IsSeriesParallel G.N G.o G.d) (hin : ∀ t : ℕ, {i | G.entry i = t}.ncard ≤ minCut G.N G.o G.d) (p : ι → List E) (hp : G.IsEquilibrium p) (t : ℕ) : G.population p t ≤ (12 * Fintype.card E) ^ Fintype.card E := by sorry

end AtomicDynRouting.ResidenceTime.Supplement
