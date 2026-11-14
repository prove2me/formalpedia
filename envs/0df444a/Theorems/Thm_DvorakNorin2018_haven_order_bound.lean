-- Prove2me | Theorems.Thm_DvorakNorin2018_haven_order_bound
-- name    : DvorakNorin2018.haven_order_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T18:26:20.345871+00:00
-- url     : https://prove2.me/theorems/fee24ffb-1553-4468-8185-759feff7af0c
-- title:
--   Balanced separators bound haven order by 15a
-- statement:
--   Let $G$ be a finite graph and let $a\ge1$ be an integer. Suppose every induced subgraph of $G$ has a balanced separation of order at most $a$: in a partition into exclusive parts $L,S,R$ with no edge from $L$ to $R$, one has $|S|\le a$ and $3|L|,3|R|\le2|V(H)|$. Then every haven of $G$ has order at most $15a$. A haven of order $k$ chooses a nonempty component of $G-W$ for every $|W|<k$, and any two chosen components touch. This is the haven-order conclusion obtained by the complete tame-cloud counting contradiction in the proof of Dvorak--Norin Theorem 1. The separate treewidth/bramble duality converts this to the treewidth bound; that duality is not an assumption or conclusion of this theorem.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Lemma 7 and Section 3, proof of Theorem 1, PDF pp. 6-9.

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
set_option autoImplicit false
open StableMSR.Recovery.Havens

namespace DvorakNorin2018
theorem haven_order_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) : k ≤ 15*a := by sorry
end DvorakNorin2018
