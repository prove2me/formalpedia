-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_hcWeight_le
-- name    : ExpanderBIS.HardCore.hcWeight_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:05.936899+00:00
-- url     : https://prove2.me/theorems/e2f6e9b9-a069-4662-9310-9857397722f6
-- title:
--   §4.2, p. 21 — every polymer weight satisfies w_γ ≤ (1 + λ)^{−α|γ|}
-- statement:
--   Let $G$ be a bipartite $\alpha$-expander ($\alpha > 0$) with classes $\mathcal O, \mathcal E$, and let $\lambda > 0$. For every even or odd polymer $\gamma$,
--   $$w_\gamma = \frac{\lambda^{|\gamma|}}{(1+\lambda)^{|\partial\gamma|}} \le (1+\lambda)^{-\alpha|\gamma|}.$$
--
--   The expansion of small sets turns into exponential decay of the polymer weights in the polymer size, which is the input of the Kotecký–Preiss verification.
--
--   **Formalization Note** The power $(1+\lambda)^{-\alpha|\gamma|}$ is a real power (`Real.rpow`); its base is at least $1$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 21, §4.2, display "w_γ = λ^{|γ|}/(1 + λ)^{|∂γ|} ≤ … ≤ (1 + λ)^{−α|γ|}"

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem hcWeight_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α lam : ℝ)
    (hα : 0 < α) (hbip : IsBipartiteWrt G O) (hG : IsBipExpander G O α) (hlam : 0 < lam)
    (side : Finset V) (hside : side = O ∨ side = univ \ O)
    (γ : Finset V) (hγ : γ ∈ sidePolymers G side) :
    hcWeight G lam γ ≤ (1 + lam) ^ (-(α * (#γ : ℝ))) := by sorry

end ExpanderBIS.HardCore
