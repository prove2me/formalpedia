-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_theorem_6_20
-- name    : ConservativeVCSP.Treewidth.theorem_6_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:48:43.075064+00:00
-- url     : https://prove2.me/theorems/907994fd-65d1-4ade-85f1-55e5d2495fe0
-- title:
--   Theorem 6.20 — fractional local necessity yields expressive sets
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a finite, finite-valued hard-list language over $D$ and $B$ a reversing block of $G_\Gamma$. Let $I$ be an instance of $\mathrm{VCSP}(\Gamma)$ such that the available set $L_v$ of each variable $v$ (1) belongs to $B$ or has size one, (2) is pairwise interacting, and (3) consists of elements that are locally fractionally necessary at $v$. Then
--   $$L_v\ \text{is expressive for every variable } v.$$
--
--   Combined with Lemma 2.12 it bounds the size of every remaining available set by $c_\Gamma$.
--
--   Differences from the source:
--   - encoding: an instance $I=(V,\mathcal C,t)$ with a finite variable set $V$ and a finite family of constraints → `Instance`: variables `Fin n`, constraints a `List` (repetitions allowed), target `t : ℚ`; reason: renaming variables changes no instance; a family is a list up to order
--   - encoding: a pairwise interacting set $S$, $|S|\ge2$, belongs to the block of $(a,b)$ for two distinct $a,b\in S$ (Definition 6.10) → `BelongsTo`: $S$ pairwise interacting, $|S|\ge 2$, and every ordered pair of distinct elements of $S$ lies in $B$ (the wording of §2.2, p. 12); reason: equivalent for finite, finite-valued hard-list languages by Lemma 2.10 (p. 34)
--   - encoding: the optimum of Linear program 6.16 is positive → `LocFracNecessary`: $a\in L_v$ and some feasible solution of (4)–(8) with the relaxed bounds has $\varepsilon>0$; reason: the program maximizes ε over a nonempty polytope, so its optimum is attained and is positive iff some feasible point has ε > 0
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 40, Theorem 6.20

import Definitions.Def_ConservativeVCSP_Treewidth_Blocks
import Definitions.Def_ConservativeVCSP_Treewidth_LocalNecessity

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Theorem 6.20 (Fractional local necessity yields expressive sets, p. 40): for a finite,
finite-valued hard-list language `Γ`, a reversing block `B` of `G_Γ` and an instance `I` of
`VCSP(Γ)` whose available sets each (1) belong to `B` or have size one, (2) are pairwise
interacting, (3) consist of locally fractionally necessary elements, every available set of `I` is
expressive. -/
theorem theorem_6_20 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D))
    (hΓ : IsFVHardListLanguage Γ) (B : Set (D × D)) (hB : IsReversingBlock Γ B)
    (I : Instance D) (hI : I.IsOver Γ)
    (h1 : ∀ v, BelongsTo Γ (I.avail v) B ∨ (I.avail v).ncard = 1)
    (h2 : ∀ v, PairwiseInteracting Γ (I.avail v))
    (h3 : ∀ v, ∀ a ∈ I.avail v, I.LocFracNecessary v a) :
    ∀ v, IsExpressive Γ (I.avail v) := by sorry

end ConservativeVCSP.Treewidth
