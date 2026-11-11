-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_corollary_6_13
-- name    : ConservativeVCSP.Treewidth.corollary_6_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:49:04.729699+00:00
-- url     : https://prove2.me/theorems/86688e50-5a36-4215-9774-466716d1e894
-- title:
--   Corollary 6.13 — all costs on products of sets in a reversing block
-- statement:
--   Let $D$ be a finite domain and $\Gamma$ a finite, finite-valued hard-list language over $D$. Let $B$ be a reversing block of $G_\Gamma$, $r\ge1$ and $S_1,\dots,S_r\subseteq D$ nonempty, such that every $S_i$ with $|S_i|\ge2$ is pairwise interacting and belongs to $B$, and $\Gamma$ expresses all finite-valued unary cost functions on each $S_i$. Then every $f:S_1\times\cdots\times S_r\to\mathbb Q_{\ge0}$ satisfies
--   $$g=f+c\ \text{ on } S_1\times\cdots\times S_r$$
--   for some finite-valued $g\in\mathrm{pow}(\Gamma)$ and $c\in\mathbb Q$.
--
--   It is the expressibility engine behind Lemma 2.12 and Theorem 6.20.
--
--   Differences from the source:
--   - encoding: $f : S_1\times\cdots\times S_r\to\mathbb Q_{\ge0}$ → `f : ((i : Fin r) → S i) → ℚ≥0`, and `g` of arity `r` with `toQ (g x) = f x + c` on the product (`ExpressesOn`); reason: Lean convention for a product of subsets
--   - encoding: a pairwise interacting set $S$, $|S|\ge2$, belongs to the block of $(a,b)$ for two distinct $a,b\in S$ (Definition 6.10) → `BelongsTo`: $S$ pairwise interacting, $|S|\ge 2$, and every ordered pair of distinct elements of $S$ lies in $B$ (the wording of §2.2, p. 12); reason: equivalent for finite, finite-valued hard-list languages by Lemma 2.10 (p. 34)
--   - encoding: cost values in $\mathbb{Q}_{\ge 0}\cup\{\infty\}$, additive shifts $c\in\mathbb{Q}$ → `WithTop ℚ≥0`; a shift is applied after the inclusion `toQ` into `WithTop ℚ` (with ∞ + c = ∞); reason: Lean convention; the same functions and the same shifts
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 36, Corollary 6.13

import Definitions.Def_ConservativeVCSP_Treewidth_Blocks

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Corollary 6.13 (Costs in a reversing block, p. 36): for a finite, finite-valued hard-list
language `Γ`, a reversing block `B` of `G_Γ` and nonempty `S₁, …, S_r` (`r ≥ 1`) such that every
`S_i` of size at least two is pairwise interacting and belongs to `B` and `Γ` expresses all
finite-valued unary cost functions on each `S_i`, every `f : S₁ × ⋯ × S_r → ℚ≥0` is a
finite-valued member of `pow(Γ)` up to a constant. -/
theorem corollary_6_13 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D))
    (hΓ : IsFVHardListLanguage Γ) (B : Set (D × D)) (hB : IsReversingBlock Γ B)
    (r : ℕ) (hr : 1 ≤ r) (S : Fin r → Set D) (hS : ∀ i, (S i).Nonempty)
    (hbelong : ∀ i, 2 ≤ (S i).ncard → PairwiseInteracting Γ (S i) ∧ BelongsTo Γ (S i) B)
    (hunary : ∀ i, ExpressesAllUnaryFV Γ (S i)) :
    ∀ f : ((i : Fin r) → S i) → ℚ≥0, ExpressesOn Γ S f := by sorry

end ConservativeVCSP.Treewidth
