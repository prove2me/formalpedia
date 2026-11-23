-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_Supplement_lemma_8
-- name    : AtomicDynRouting.ResidenceTime.Supplement.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:34:17.805383+00:00
-- url     : https://prove2.me/theorems/c46918ce-de7e-4493-be23-98780e0489b1
-- title:
--   Lemma 8, p. 24 — at a UFR equilibrium of Γ1 or Γ2 no lower-priority agent preempts a higher-priority one, and each agent has a path on which no lower-priority agent can preempt him
-- statement:
--   Consider an ADR game $\Gamma_1$ or $\Gamma_2$ on a finite acyclic unit-capacity network with a single OD pair $(o,d)$, finitely many agents entering at each integer time, and a global agent-priority list (a complete ordering in which earlier entrants have higher priority). Let $p$ be a UFR equilibrium and $\lambda$ an arbitrary agent.
--
--   1. Under $p$, no agent with a lower priority can preempt an agent with a higher priority.
--   2. There is an $o$-$d$ path $P^*_\lambda\in\mathcal P$ such that, if all agents with higher priorities than $\lambda$ follow their routes in $p$ and $\lambda$ follows $P^*_\lambda$, then, whatever $o$-$d$ paths the agents of lower priority choose, none of them preempts $\lambda$ at any vertex of $P^*_\lambda$.
--
--   Part 1 is Lemma 2 of §5.2; together the two parts give Theorem 3 for $\Gamma_1$ and $\Gamma_2$.
--
--   Differences from the source:
--
--   - encoding: the three games of §5.1 with their priority lists → Game with Rule r1/r2/r3; priorities as strict total orders (Γ3: an order of all of E per vertex, one global original order) and the run built by recursion on time; reason: only the restrictions to incoming edges and to each Δ_r are used, and every family of such orders is a restriction; the recursion is the deterministic dynamics the rules determine
--   - encoding: arrival times t^v_j(p), ∞ off the route → ℕ∞-valued arrTime (⊤ off the route); reason: Lean convention; same values
--   - reading: 'no matter how other agents choose their routes, none of them can preempt λ' → every agent j of lower priority than λ (hp λ j) chooses any o-d path, and no such j preempts λ; reason: the agents of higher priority are the ones fixed to p, and they may preempt λ; the 'other agents' are the remaining ones, which are exactly the lower-priority agents under a strict total priority order
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 24 (PDF 25), Appendix C, Lemma 8 (= Lemma 2, p. 14, for part (i))

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem lemma_8 {ι V E : Type} [Fintype V] [Fintype E] (G : Game ι V E) (hN : G.N.Acyclic) (hG : G.Standing) (hp : ι → ι → Prop) (hrule : G.rule = .r1 hp ∨ G.rule = .r2 hp) (p : ι → List E) (hpU : G.IsUFR p) :
    (∀ i j, hp i j → ∀ v, ¬ G.preempts p j i v) ∧
    (∀ l : ι, ∃ P : List E, G.IsODPath P ∧
      ∀ q : ι → List E, G.IsProfile q → (∀ k, hp k l → q k = p k) → q l = P →
        ∀ j, hp l j → ∀ v, ¬ G.preempts q j l v) := by sorry

end AtomicDynRouting.ResidenceTime.Supplement
