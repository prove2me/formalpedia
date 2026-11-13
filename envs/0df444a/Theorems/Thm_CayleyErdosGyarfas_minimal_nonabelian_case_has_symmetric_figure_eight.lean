-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_minimal_nonabelian_case_has_symmetric_figure_eight
-- name    : CayleyErdosGyarfas.minimal_nonabelian_case_has_symmetric_figure_eight
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T02:39:38.206582+00:00
-- url     : https://prove2.me/theorems/93e39e68-049d-4290-8393-03c362fdc587
-- title:
--   Minimal case of the proof of Theorem 1.1
-- statement:
--   Let $G$ be a finite nonabelian group of odd order, and let $S \subseteq G$ be closed under inverses with $1 \notin S$. Suppose that $G/A$ is cyclic for every nontrivial abelian normal subgroup $A \trianglelefteq G$, and that $S$ contains two noncommuting elements $s, t$ that generate $G$:
--
--   $$\langle s, t \rangle = G, \qquad st \ne ts .$$
--
--   Then $\operatorname{Cay}(G,S)$ contains a symmetric figure-eight. Here $\operatorname{Cay}(G,S)$ has vertex set $G$, distinct $g, h$ being adjacent when $h = gu$ or $g = hu$ for some $u \in S$, and a symmetric figure-eight is a pair of cycles of a common length $2^n$, $n \ge 2$, that meet in exactly one vertex, one a left translate of the other up to the choice of starting vertex (definition `CayleyErdosGyarfas_HasSymmetricFigureEight`).
--
--   This is the situation to which the proof of Theorem 1.1 of the source paper reduces a minimal counterexample to the noncyclic claim (every Cayley graph of a noncyclic group of odd order has a symmetric figure-eight). Together with the induction on $|G|$, it yields that claim.
--
--   **Formalization Note** The quotient hypothesis ranges over all subgroups `A` with `[A.Normal]`, `[IsMulCommutative A]` and `A ≠ ⊥`. Nonabelianness is `¬ IsMulCommutative G`. The set $S$ is not required to generate $G$; generation is assumed for the pair $\{s, t\}$.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (https://arxiv.org/abs/2611.05060v1), §2, p. 4, proof of Theorem 1.1 (reduction of a minimal counterexample). Lean statement: https://github.com/burkh4rt/Cayley-Erdos-Gyarfas-Formalized/blob/111aa033acfab934208ce6b2e0cebecacfd6bd24/CayleyErdosGyarfas/OddOrderMain.lean#L19-L46 (Palomar entry PALOMAR-2026-11-04-000015).

import Definitions.Def_CayleyErdosGyarfas_HasSymmetricFigureEight
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Finite

namespace CayleyErdosGyarfas

theorem minimal_nonabelian_case_has_symmetric_figure_eight
    {G : Type*} [Group G] [Finite G] (S : Set G)
    (hodd : Odd (Nat.card G)) (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (_hone : (1 : G) ∉ S) (hncomm : ¬ IsMulCommutative G)
    (hquot : ∀ (A : Subgroup G) [A.Normal] [IsMulCommutative A],
      A ≠ ⊥ → IsCyclic (G ⧸ A))
    {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hst : ¬ Commute s t)
    (hpair : Subgroup.closure ({s, t} : Set G) = ⊤) :
    HasSymmetricFigureEight S := by sorry

end CayleyErdosGyarfas
