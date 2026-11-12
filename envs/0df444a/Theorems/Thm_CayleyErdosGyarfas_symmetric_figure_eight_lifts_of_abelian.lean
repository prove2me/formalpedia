-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_symmetric_figure_eight_lifts_of_abelian
-- name    : CayleyErdosGyarfas.symmetric_figure_eight_lifts_of_abelian
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:10:23.673871+00:00
-- url     : https://prove2.me/theorems/e1246fa9-961a-4152-9a60-fe334119e87d
-- title:
--   Lemma 1.2: symmetric figure-eights lift through abelian normal subgroups
-- statement:
--   Let $G$ be a finite group of odd order and let $S \subseteq G$ be a generating set of $G$ that is closed under inverses and does not contain the identity. Let $A \trianglelefteq G$ be an abelian normal subgroup, and write
--
--   $$\overline{S} = \{ sA : s \in S \} \setminus \{ A \} \subseteq G/A$$
--
--   for the image of $S$ in $G/A$ with the identity coset removed. Then
--
--   $$\operatorname{Cay}(G/A, \overline{S}) \text{ contains a symmetric figure-eight} \;\Longrightarrow\; \operatorname{Cay}(G, S) \text{ contains a symmetric figure-eight}.$$
--
--   A symmetric figure-eight is a pair of cycles of a common length $2^n$, $n \ge 2$, that share exactly one vertex, one of which is a left translate of the other up to the choice of starting vertex (definition `CayleyErdosGyarfas_HasSymmetricFigureEight`). The cycle lengths upstairs and downstairs may differ. Here, for a group $H$ and a subset $T \subseteq H$, $\operatorname{Cay}(H,T)$ is the Cayley graph with vertex set $H$ in which distinct $x, y \in H$ are adjacent when $y = xt$ or $x = yt$ for some $t \in T$; every left multiplication $z \mapsto hz$ is an automorphism of it. A cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   In the paper this lemma drives the induction on $|G|$ in the proof of Theorem 1.1, through quotients by abelian normal subgroups.
--
--   **Formalization Note** The kernel hypotheses are `[A.Normal]` and `[IsMulCommutative A]`, and the quotient generating set is `(QuotientGroup.mk (s := A)) '' S \ {1}`. Removing the identity coset matches the paper and does not change the quotient graph, which has no loops. The statement is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.symmetric_figure_eight_lifts_of_abelian` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015, where it is proved.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 2, Lemma 1.2 (proof in §2, pp. 2–3); standing conventions of §1.1, p. 2. Lean statement as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

namespace CayleyErdosGyarfas

/-- **Lemma 1.2** (arXiv:2611.05060v1, p. 2). Let `G = ⟨S⟩` be a finite group of odd
order, with `S` symmetric and `1 ∉ S`, and let `A` be an abelian normal subgroup. Put
`S̄ = {sA : s ∈ S} \ {A}`. If `Cay(G/A, S̄)` contains a symmetric figure-eight, then
so does `Cay(G, S)`. -/
theorem symmetric_figure_eight_lifts_of_abelian
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G))
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S)
    (hgen : Subgroup.closure S = ⊤)
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hfigure : HasSymmetricFigureEight
      ((QuotientGroup.mk (s := A)) '' S \ {1})) :
    HasSymmetricFigureEight S := by sorry

end CayleyErdosGyarfas
