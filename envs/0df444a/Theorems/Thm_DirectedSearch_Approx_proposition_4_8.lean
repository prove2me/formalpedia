-- Prove2me | Theorems.Thm_DirectedSearch_Approx_proposition_4_8
-- name    : DirectedSearch.Approx.proposition_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:21.689495+00:00
-- url     : https://prove2.me/theorems/8f05d563-ff47-47d9-8cc2-ed6aa90d1be1
-- title:
--   Proposition 4.8, p. 24 — in a star-shaped market some stationary equilibrium attains half the first-best welfare
-- statement:
--   Consider a market satisfying the standing assumptions that is **star-shaped**: one side consists of a single type. Then there is a choice of assortments, with thresholds, matching rates and masses satisfying (6a)–(6f) — an induced stationary equilibrium — whose welfare $\mathrm{SW}$ satisfies
--   $$\mathrm{FB}(Q)\le 2\,\mathrm{SW}$$
--   for the welfare $\mathrm{FB}(Q)$ of **every** first-best feasible candidate $Q$.
--
--   This is Step (3) of the approximation, applied to each star-shaped submarket.
--
--   **Formalization Note.** Star-shaped is `Fintype.card M = 1 ∨ Fintype.card W = 1`; the paper's "without loss of generality $\mathcal M=\{m\}$" is a proof device, so both sides are covered. The 2-approximation to the first-best optimum is stated against every first-best feasible candidate, which avoids a supremum.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 24, Proposition 4.8

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

namespace DirectedSearch.Approx
theorem proposition_4_8 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (hstar : Fintype.card M = 1 ∨ Fintype.card W = 1) :
    ∃ P : Profile M W, SecondBestFeasible mk P ∧
      ∀ Q : FBProfile M W, FirstBestFeasible mk Q → fbWelfare mk Q ≤ 2 * sbWelfare mk P := by sorry
end DirectedSearch.Approx
