-- Prove2me | Theorems.Thm_DirectedSearch_Approx_theorem_4_1
-- name    : DirectedSearch.Approx.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:15.57935+00:00
-- url     : https://prove2.me/theorems/49540df3-0d5f-4f64-8fd6-9600d96640c6
-- title:
--   Theorem 4.1, p. 18 — some assortments induce a stationary equilibrium with at least 1/4 of the first-best welfare
-- statement:
--   Consider a directed-search market satisfying the standing assumptions: finitely many types on each side, $\delta>0$, $\alpha_\theta>0$, and atomless utility laws $F_{mw}$ with finite mean. Then the platform can choose assortments $\lambda$ that induce a stationary equilibrium — together with thresholds $\tau$, matching rates $\xi$ and masses $\eta$ they satisfy (6a)–(6f), the best-response constraint (6e) included — whose welfare $\mathrm{SW}$ satisfies
--   $$\mathrm{FB}(Q)\le 4\,\mathrm{SW}$$
--   for the welfare $\mathrm{FB}(Q)$ of **every** first-best feasible candidate $Q$ (pairwise thresholds $\tau_{mw}$, no incentive constraint).
--
--   This is the parenthetical of Theorem 4.1: the equilibrium is a 4-approximation to the platform's first-best optimal welfare, and a fortiori to the optimum of OptimalDirectedSearch, since every second-best feasible candidate yields a first-best feasible one with the same welfare.
--
--   **Formalization Note.** The "polynomial-time" part of the theorem is not formalized: the paper's computational model (oracle access to the laws, footnote 15) is not pinned down. The comparison is stated against every first-best feasible candidate rather than through a supremum. With $\mathcal M$ or $\mathcal W$ empty both welfares are 0 and the statement holds, as in the paper.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 18, Theorem 4.1 (parenthetical: 4-approximation to the first-best optimal welfare)

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx
theorem theorem_4_1 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      ∀ Q : FBProfile M W, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 4 * sbWelfare mk P := by sorry
end DirectedSearch.Approx
