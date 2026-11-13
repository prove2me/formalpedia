-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_nilpotent_cayley_contains_two_power_cycle
-- name    : CayleyErdosGyarfas.nilpotent_cayley_contains_two_power_cycle
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:11:37.541672+00:00
-- url     : https://prove2.me/theorems/92d5fe39-ff2c-4c37-9231-04c7ee6ec843
-- title:
--   Corollary 1.4: Cayley graphs of finite nilpotent groups satisfy Erdős–Gyárfás
-- statement:
--   Let $G$ be a finite nilpotent group and let $S \subseteq G$ be a generating set of $G$ that is closed under inverses, does not contain the identity, and has at least three elements. Then
--
--   $$\exists\, n \ge 2 : \quad \operatorname{Cay}(G,S) \text{ contains a cycle of length } 2^n .$$
--
--   Here, for a group $H$ and a subset $T \subseteq H$, $\operatorname{Cay}(H,T)$ is the Cayley graph with vertex set $H$ in which distinct $x, y \in H$ are adjacent when $y = xt$ or $x = yt$ for some $t \in T$; every left multiplication $z \mapsto hz$ is an automorphism of it. A cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   Finite nilpotent groups include all finite abelian groups and all finite $p$-groups. Theorem 1.1 of the same paper gives this conclusion for groups of odd order. Neither hypothesis contains the other: groups of odd order need not be nilpotent (for example $C_7 \rtimes C_3$), and nilpotent groups may have even order. The corollary therefore extends the conclusion of Theorem 1.1 to finite nilpotent groups of even order.
--
--   **Formalization Note** Nilpotency is Mathlib's `Group.IsNilpotent G`: the upper central series reaches $G$. Odd order is not assumed. Generation is `Subgroup.closure S = ⊤`, $|S|$ is `S.ncard`, the graph is Mathlib's `SimpleGraph.mulCayley S`, a cycle is a closed walk with `IsCycle`, and the bound $n \ge 2$ is kept to match the paper. The statement is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.nilpotent_cayley_contains_two_power_cycle` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015, where it is proved.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 2, Corollary 1.4 (proof in §3, p. 6); standing conventions of §1.1, p. 2; power-of-two length in the sense of §1, p. 1 (a simple cycle of length 2^n, n ≥ 2). Lean statement as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

namespace CayleyErdosGyarfas

/-- **Corollary 1.4** (arXiv:2611.05060v1, p. 2). If `G` is a finite nilpotent group and
`S` is a symmetric generating set with `1 ∉ S` and `|S| ≥ 3`, then `Cay(G, S)` contains a
simple cycle of length `2 ^ n` for some `n ≥ 2`. -/
theorem nilpotent_cayley_contains_two_power_cycle
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G] (S : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (hcard : 3 ≤ S.ncard) :
    ∃ (n : ℕ) (v : G) (c : (SimpleGraph.mulCayley S).Walk v v),
      2 ≤ n ∧ c.IsCycle ∧ c.length = 2 ^ n := by sorry

end CayleyErdosGyarfas
