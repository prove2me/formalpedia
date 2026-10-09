-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_lemma_20
-- name    : ExpanderBIS.HardCore.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:30.369488+00:00
-- url     : https://prove2.me/theorems/3412a98f-50bf-4ced-812c-74823af8d66b
-- title:
--   Lemma 20 — for λ > e^{11/α}, (1 + λ)^{|𝒪|}Ξ^ℰ + (1 + λ)^{|ℰ|}Ξ^𝒪 is an e^{−n}-relative approximation to Z_G(λ)
-- statement:
--   Let $G$ be a bipartite $\alpha$-expander ($\alpha > 0$) with classes $\mathcal O, \mathcal E$ on $n \ge 3$ vertices, and let $\lambda > e^{11/\alpha}$. Then
--   $$\tilde Z_G(\lambda) = (1+\lambda)^{|\mathcal O|}\,\Xi^{\mathcal E}(G) + (1+\lambda)^{|\mathcal E|}\,\Xi^{\mathcal O}(G)$$
--   is an $e^{-n}$-relative approximation to $Z_G(\lambda)$:
--   $$e^{-e^{-n}}\,\tilde Z_G(\lambda) \le Z_G(\lambda) \le e^{e^{-n}}\,\tilde Z_G(\lambda).$$
--
--   This is the reduction step of Theorem 1: approximating the hard-core partition function on a bipartite expander reduces to approximating two polymer partition functions. The even polymers describe deviations from the all-odd ground state, hence the factor $(1+\lambda)^{|\mathcal O|}$ in front of $\Xi^{\mathcal E}$.
--
--   **Formalization Note** $n \ge 3$ is added for the reason given in Lemma 18. The relative approximation is Definition 10 of the paper.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 19, Lemma 20

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem lemma_20 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α lam : ℝ)
    (hα : 0 < α) (hn : 3 ≤ Fintype.card V)
    (hbip : IsBipartiteWrt G O) (hG : IsBipExpander G O α)
    (hlam : Real.exp (11 / α) < lam) :
    ExpanderBIS.Potts.IsRelApprox (Real.exp (-(Fintype.card V : ℝ)))
      ((1 + lam) ^ #O * sideXi G (univ \ O) lam + (1 + lam) ^ #(univ \ O) * sideXi G O lam)
      (hardcoreZ G lam) := by sorry

end ExpanderBIS.HardCore
