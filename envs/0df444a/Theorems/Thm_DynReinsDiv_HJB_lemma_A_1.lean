-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_1
-- name    : DynReinsDiv.HJB.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:33.295775+00:00
-- url     : https://prove2.me/theorems/79080290-9009-4550-8ea9-123b5d6a566f
-- title:
--   Lemma A.1 — F(y, z) = A(−y/z) and G(y, z) = B(−y/z) are uniformly Lipschitz on (−∞, ∞) × [1, ∞)
-- statement:
--   Let $A$, $B$ be the functions (A.5), (A.6) of a model with tail assumption (3.3), and define
--   $$F(y,z)=A\Big(-\frac yz\Big),\qquad G(y,z)=B\Big(-\frac yz\Big).$$
--   Then $F$ and $G$ are Lipschitz continuous on $(-\infty,\infty)\times[1,\infty)$: there is a constant $K$ with
--   $$|F(y,z)-F(y',z')|\le K\,\|(y,z)-(y',z')\|,\qquad |G(y,z)-G(y',z')|\le K\,\|(y,z)-(y',z')\|$$
--   for all $(y,z),(y',z')$ in that set.
--
--   Applied with $y=u_x$ and $z=u\ge1$, it makes the coefficients $A(-u_x/u)$, $B(-u_x/u)$ of the penalized equation (A.17) Lipschitz in $(u_x,u)$, which the comparison principle (Lemma A.2) needs.
--
--   **Formalization Note** Lemma A.1's $F$ and $G$ are `FA` and `GB` (the paper's $F$ is also the claim distribution function). The norm on $\mathbb R^2$ is the maximum norm; Lipschitz continuity does not depend on that choice.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 25, Lemma A.1

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

namespace DynReinsDiv.HJB

theorem lemma_A_1 (M : Model) :
    (∃ K : NNReal, LipschitzOnWith K (fun yz : ℝ × ℝ => M.FA yz.1 yz.2) (Set.univ ×ˢ Set.Ici 1)) ∧
    (∃ K : NNReal, LipschitzOnWith K (fun yz : ℝ × ℝ => M.GB yz.1 yz.2) (Set.univ ×ˢ Set.Ici 1)) := by sorry

end DynReinsDiv.HJB
