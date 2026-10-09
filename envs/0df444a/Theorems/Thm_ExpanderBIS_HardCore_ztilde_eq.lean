-- Prove2me | Theorems.Thm_ExpanderBIS_HardCore_ztilde_eq
-- name    : ExpanderBIS.HardCore.ztilde_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:02.418694+00:00
-- url     : https://prove2.me/theorems/198b38a8-477d-4b7e-b483-99de98decdbd
-- title:
--   §4.1, p. 20 — Z̃_G(λ) = Z_G(λ) + Σ_{I sparse} λ^{|I|}
-- statement:
--   Let $G$ be a bipartite $\alpha$-expander ($\alpha > 0$) with classes $\mathcal O, \mathcal E$ on $n \ge 3$ vertices, and let $\lambda > 0$. Then
--   $$(1+\lambda)^{|\mathcal O|}\,\Xi^{\mathcal E}(G) + (1+\lambda)^{|\mathcal E|}\,\Xi^{\mathcal O}(G) = Z_G(\lambda) + \sum_{I \text{ sparse}} \lambda^{|I|},$$
--   where the last sum runs over the independent sets $I$ of $G$ for which both $I \cap \mathcal O$ and $I \cap \mathcal E$ are sparse (all their $G^2$-connected components are small).
--
--   In words, the two polymer expansions together count every independent set once, and the sparse ones twice. It is the exact identity behind Lemma 20.
--
--   **Formalization Note** $n \ge 3$ is added for the reason given in Lemma 18, on which the identity rests. $\lambda > 0$ is the paper's standing assumption on the fugacity; it also keeps $1+\lambda \ne 0$ in the weights.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 20, §4.1, proof of Lemma 20, display "Z̃_G(λ) = Z_G(λ) + Σ_{I sparse} λ^{|I|}"

import Mathlib
import Definitions.Def_ExpanderBIS_HardCore_Setting

namespace ExpanderBIS.HardCore

open Finset

theorem ztilde_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (O : Finset V) (α lam : ℝ)
    (hα : 0 < α) (hn : 3 ≤ Fintype.card V)
    (hbip : IsBipartiteWrt G O) (hG : IsBipExpander G O α) (hlam : 0 < lam) :
    (1 + lam) ^ #O * sideXi G (univ \ O) lam + (1 + lam) ^ #(univ \ O) * sideXi G O lam
      = hardcoreZ G lam + sparseIndepSum G O lam := by sorry

end ExpanderBIS.HardCore
