-- Prove2me | Theorems.Thm_FlowAllocGames_StrongPoA_strong_poa_le
-- name    : FlowAllocGames.StrongPoA.strong_poa_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:15.402771+00:00
-- url     : https://prove2.me/theorems/10cbeb23-62b0-4723-8139-e936cfa26402
-- title:
--   Theorem 16, p. 30 — in unit-ranking games the price of anarchy for strong equilibria in terms of Flow is at most d
-- statement:
--   Let $\Gamma=(G,(b_v),(c_e))$ be a flow allocation game with circulation network $G'$. For an optimal circulation $f^*$ of $G'$ and a decomposition $\mathcal C(f^*)$ of $f^*$ into cycles of unit flow, let
--   $$d=\min_{f^*,\,\mathcal C(f^*)}\ \max_{C_i\in\mathcal C(f^*)}|C_i|$$
--   be the min-max size of a cycle, over all decompositions of all optimal circulations; cycle sizes count the auxiliary edges $(v,s)$ and $(s,v)$.
--
--   **Theorem 16.** In unit-ranking games, the price of anarchy for strong equilibria in terms of $\mathrm{Flow}$ is at most $d$: for every strong equilibrium $\mathbf a$ and every unit-ranking profile $\mathbf a'$,
--   $$\mathrm{Flow}(\mathbf a')\le d\cdot\mathrm{Flow}(\mathbf a).$$
--
--   Since a strong equilibrium maximizing $\mathrm{Flow}$ always exists (Theorem 9), the price of stability is $1$, and this theorem bounds how far the worst strong equilibrium can fall below the optimum by a structural parameter of the network. Proposition 17 shows the bound is tight up to one.
--
--   **Formalization Note** The statement is quantified over every optimal circulation $f^*$, every decomposition $\mathcal C(f^*)$ into unit-flow cycles and every $d$ bounding the sizes of its cycles; the least such $d$ is the paper's min-max $d$, which is attained because only finitely many decompositions exist, so this is equivalent to the bound for the min-max $d$ and avoids an infimum that would be $0$ on an empty set. The price of anarchy (7) is stated multiplicatively, $\mathrm{Flow}(\mathbf a^*)\le d\cdot\mathrm{Flow}(\mathbf a)$, so that $\mathrm{Flow}(\mathbf a)=0$ forces $\mathrm{Flow}(\mathbf a')=0$; the optimal profile $\mathbf a^*$ is replaced by every unit-ranking profile $\mathbf a'$, which is equivalent. The printed proof covers the cycles of $\mathcal C(f^*)$ that avoid $s$; for cycles through $s$ its last display is false as printed (see the milestone on that display), so cycles through $s$ need a separate count. Self-loops and parallel edges are allowed, as in the paper.
-- source:
--   arXiv:1908.01714v3, Theorem 16, p. 30 (d defined above it, p. 30; price of anarchy (7), p. 15; Flow (8), p. 16)

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model
import Definitions.Def_FlowAllocGames_StrongPoA_Cycles

namespace FlowAllocGames.StrongPoA

open Game

/-- Theorem 16, p. 30 (arXiv:1908.01714v3): in unit-ranking games, the price of anarchy for strong
equilibria in terms of Flow is at most `d`, the min-max cycle size over all unit-cycle decompositions
of all optimal circulations of `G′`. Stated multiplicatively: for every optimal circulation `x`, every
decomposition `C(f*)` of `x` into unit-flow cycles of size at most `d`, every strong equilibrium `a`
and every unit-ranking profile `a′`, `Flow(a′) ≤ d · Flow(a)`. The least admissible `d` is the
paper's min-max `d`. -/
theorem strong_poa_le {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (Cs : List (List (ExtEdge V E))) (hCs : G.IsUnitCycleDecomposition x Cs)
    (d : ℕ) (hd : ∀ C ∈ Cs, C.length ≤ d)
    (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a) (a' : FlowAllocGames.StrongEq.Profile E) (ha' : G.IsUnitRanking a') :
    G.flow a' ≤ d * G.flow a := by sorry

end FlowAllocGames.StrongPoA
