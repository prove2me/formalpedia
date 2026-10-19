-- Prove2me | Theorems.Thm_AtomicDynFlow_IDNE_theorem_1
-- name    : AtomicDynFlow.IDNE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:01.955179+00:00
-- url     : https://prove2.me/theorems/8291b610-2eb8-4f6c-a10e-dbb2488ceb1d
-- title:
--   Theorem 1, p. 12 (PDF 13) — every normal-form game Γ^N admits an iteratively dominant NE (which is an NE)
-- statement:
--   Let $\Gamma^N$ be an atomic dynamic flow game of nonadaptive agents: a finite acyclic directed multigraph with destination $d$ reachable from every vertex, unit capacities and lengths, a complete priority order on the edges entering each vertex, initial ranked queues at time $0$ and finite ranked inflows $\Delta_{r,v}$ at times $r\ge1$ (the agent set may be infinite), with the edge-priority deterministic-queuing rule (R0)–(R4).
--
--   **Theorem 1.** Every such game admits an iteratively dominant NE (IDNE), and this profile is a Nash equilibrium:
--   $$\exists\,p=(P_i)_{i\in\Delta},\ P_i\in\mathcal P_i:\qquad p \text{ is an IDNE of }\Gamma^N\ \text{ and an NE of }\Gamma^N .$$
--
--   This is the main existence result of the paper for nonadaptive agents. In contrast with agent-priority tie-breaking (Example 3, where no NE need exist with several origins), edge priorities guarantee an equilibrium for every network, every pattern of inflows and every number of origins.
--
--   **Formalization Note.** The NE conjunct is the paper's own claim (§4.1, p. 11: an IDNE "is still an NE"; p. ec3: "it is actually an NE"), made explicit. No finiteness of the agent set is assumed.
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. 12 (PDF 13), Theorem 1; p. 11 (PDF 12), §4.1; p. ec3 (PDF 35)

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium

namespace AtomicDynFlow.IDNE
theorem theorem_1 {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) :
    ∃ p : A → List E, (∀ a, G.IsStrategy a (p a)) ∧ G.IsIDNE p ∧ G.IsNE p := by sorry
end AtomicDynFlow.IDNE
