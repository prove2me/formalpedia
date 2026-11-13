-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_noncyclic_odd_order_symmetric_figure_eight
-- name    : CayleyErdosGyarfas.noncyclic_odd_order_symmetric_figure_eight
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:10:36.3414+00:00
-- url     : https://prove2.me/theorems/236b9665-ed73-4171-bf69-5301c2799ea8
-- title:
--   Symmetric figure-eights in Cayley graphs of noncyclic groups of odd order
-- statement:
--   Let $G$ be a finite noncyclic group of odd order and let $S \subseteq G$ be a generating set of $G$ that is closed under inverses and does not contain the identity. Then
--
--   $$\operatorname{Cay}(G,S) \text{ contains a symmetric figure-eight},$$
--
--   that is, two cycles of a common length $2^n$ with $n \ge 2$ that share exactly one vertex, one of which is the left translate $g\alpha$ of the other cycle $\alpha$ for some $g \in G$, up to the choice of starting vertex. Here, for a group $H$ and a subset $T \subseteq H$, $\operatorname{Cay}(H,T)$ is the Cayley graph with vertex set $H$ in which distinct $x, y \in H$ are adjacent when $y = xt$ or $x = yt$ for some $t \in T$; every left multiplication $z \mapsto hz$ is an automorphism of it. A cycle of length $k$ is a closed walk $(v_0, v_1, \dots, v_k = v_0)$ with $k \ge 3$ whose vertices $v_1, \dots, v_k$ are pairwise distinct.
--
--   The paper announces this after Theorem 1.1 (every Cayley graph of a noncyclic group of odd order contains a symmetric figure-eight) and proves it as the claim inside the proof of Theorem 1.1. It strengthens Theorem 1.1 for noncyclic groups. The restriction to noncyclic groups is needed: for $C_5 = \langle c \rangle$, $\operatorname{Cay}(C_5, \{c^{\pm 1}, c^{\pm 2}\}) = K_5$ has too few vertices for two such cycles.
--
--   **Formalization Note** The paper's claim assumes $|S| \ge 3$; that hypothesis is omitted because the others imply $|S| \ge 4$. In a group of odd order no nonidentity element is its own inverse, so $S$ is a union of pairs $\{s, s^{-1}\}$ with $s \ne s^{-1}$; the empty set generates the trivial group and a single pair generates $\langle s \rangle$, both cyclic, so $S$ contains at least two pairs. Noncyclicity is `¬ IsCyclic G`. The statement is identical, up to the spelling of the namespace, to `CayleyErdősGyárfás.noncyclic_odd_order_symmetric_figure_eight` in the Challenge of Palomar entry PALOMAR-2026-11-04-000015, where it is proved.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §1, p. 1 (paragraph following Theorem 1.1) and the claim at the start of the second paragraph of the proof of Theorem 1.1 (after the cyclic case), §2, p. 4; standing conventions of §1.1, p. 2. Lean statement as in the Challenge of Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Set.Card

namespace CayleyErdosGyarfas

/-- **Noncyclic strengthening of Theorem 1.1** (arXiv:2611.05060v1, p. 1 after
Theorem 1.1, and the claim in the proof of Theorem 1.1 on p. 4). If `G` is a finite
noncyclic group of odd order and `S` is a symmetric generating set with `1 ∉ S`, then
`Cay(G, S)` contains a symmetric figure-eight. -/
theorem noncyclic_odd_order_symmetric_figure_eight
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (hone : (1 : G) ∉ S) (hgen : Subgroup.closure S = ⊤)
    (hncyclic : ¬ IsCyclic G) : HasSymmetricFigureEight S := by sorry

end CayleyErdosGyarfas
