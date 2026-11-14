-- Prove2me | Theorems.Thm_DvorakNorin2018_balanced_separators_treewidth
-- name    : DvorakNorin2018.balanced_separators_treewidth
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T18:28:03.406337+00:00
-- url     : https://prove2.me/theorems/42096793-a282-498c-974c-361c08669024
-- title:
--   Theorem 1: balanced separators bound treewidth by 15a
-- statement:
--   Let $G$ be a finite graph and let $a\ge0$ be an integer. Suppose every induced subgraph $H$ has a separation into three disjoint parts $L,S,R$ with no edge from $L$ to $R$, with $|S|\le a$ and $3|L|,3|R|\le2|V(H)|$. Then $G$ has treewidth at most $15a$: there exists a finite tree decomposition in which every bag has size at most $15a+1$. This is the balanced-separator theorem needed to convert the clustering interaction graph separator estimates into a tree decomposition. The zero-parameter and empty-graph cases are included.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Theorem 1 (PDF p. 2), with proof in Section 3, PDF pp. 8-9. Using every induced subgraph is equivalent here to every subgraph, since deleting edges preserves separators.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

namespace DvorakNorin2018
theorem balanced_separators_treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a : ℕ) (hsep : HasBalancedSeparations G a) :
    TreewidthLE G (15*a) := by sorry
end DvorakNorin2018
