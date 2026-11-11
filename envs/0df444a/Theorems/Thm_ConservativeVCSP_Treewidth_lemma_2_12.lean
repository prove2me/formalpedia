-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_lemma_2_12
-- name    : ConservativeVCSP.Treewidth.lemma_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:48:47.198595+00:00
-- url     : https://prove2.me/theorems/1df61e5a-e26f-433c-a0d1-197a09a63b1f
-- title:
--   Lemma 2.12 — c_Γ is the largest expressive set in a reversing block (or 1)
-- statement:
--   Let $D$ be a finite domain and $\Gamma$ a finite, finite-valued hard-list language over $D$. Then
--   $$c_\Gamma=\max\big(\{1\}\cup\{|S| : S\subseteq D\text{ is expressive and belongs to a reversing block of }G_\Gamma\}\big).$$
--
--   It ties the running time base, defined through binary disequality functions in $\mathrm{pow}(\Gamma)$, to the structural objects the algorithm works with.
--
--   Differences from the source:
--   - encoding: $c_\Gamma=\max(\{1\}\cup\{\dots\})$ → `IsGreatest ({1} ∪ {k | ∃ S, … ∧ S.ncard = k}) (cGamma Γ)`; reason: the set is finite and nonempty, so this is its maximum
--   - encoding: a pairwise interacting set $S$, $|S|\ge2$, belongs to the block of $(a,b)$ for two distinct $a,b\in S$ (Definition 6.10) → `BelongsTo`: $S$ pairwise interacting, $|S|\ge 2$, and every ordered pair of distinct elements of $S$ lies in $B$ (the wording of §2.2, p. 12); reason: equivalent for finite, finite-valued hard-list languages by Lemma 2.10 (p. 34)
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 37, Lemma 2.12

import Definitions.Def_ConservativeVCSP_Treewidth_Blocks

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Lemma 2.12 (p. 37): for a finite, finite-valued hard-list language `Γ`,
`c_Γ = max({1} ∪ {|S| : S ⊆ D expressive and belonging to a reversing block of G_Γ})`. -/
theorem lemma_2_12 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D))
    (hΓ : IsFVHardListLanguage Γ) :
    IsGreatest ({1} ∪ {k : ℕ | ∃ S : Set D, IsExpressive Γ S ∧
        (∃ B : Set (D × D), IsReversingBlock Γ B ∧ BelongsTo Γ S B) ∧ S.ncard = k})
      (cGamma Γ) := by sorry

end ConservativeVCSP.Treewidth
