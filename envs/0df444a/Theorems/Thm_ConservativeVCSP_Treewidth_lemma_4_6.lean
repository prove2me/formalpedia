-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_lemma_4_6
-- name    : ConservativeVCSP.Treewidth.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:47:42.007239+00:00
-- url     : https://prove2.me/theorems/53c10a34-d1d6-4961-bfe5-e4a682da3489
-- title:
--   Lemma 4.6 — an interaction witness gives a finite-valued move
-- statement:
--   Let $D$ be a finite domain and $\Gamma$ a constraint language over $D$. Suppose $a,b\in D$ interact, witnessed by distinct $c,d\in D$ and a finite-valued binary $f\in\mathrm{pow}(\Gamma)$ (neither of $a,b$ and neither of $c,d$ dominates the other, and $f(a,c)-f(b,c)\ne f(a,d)-f(b,d)$). Then
--   $$f(a,c)-f(b,c)<f(a,d)-f(b,d)\ \Longrightarrow\ (a,b)\rightsquigarrow(c,d),$$
--   otherwise $(a,b)\rightsquigarrow(d,c)$, with finite-valued moves; in any case $\{a,b\}\rightsquigarrow\{c,d\}$.
--
--   This is the link between interaction and moves; it is used to build the move graph and throughout §6.
--
--   Differences from the source:
--   - encoding: $f(a,c)-f(b,c)<f(a,d)-f(b,d)$ → `f a c + f b d < f a d + f b c` in `WithTop ℚ≥0`; reason: f is finite-valued, so the rearrangement is exact
--   - encoding: cost values in $\mathbb{Q}_{\ge 0}\cup\{\infty\}$, additive shifts $c\in\mathbb{Q}$ → `WithTop ℚ≥0`; a shift is applied after the inclusion `toQ` into `WithTop ℚ` (with ∞ + c = ∞); reason: Lean convention; the same functions and the same shifts
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 21, Lemma 4.6

import Definitions.Def_ConservativeVCSP_Treewidth_Moves

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Lemma 4.6 (p. 21): an interaction of `a, b` witnessed by `c, d` and a finite-valued binary
`f ∈ pow(Γ)` gives a finite-valued move `(a, b) ⇝ (c, d)` if `f(a,c) − f(b,c) < f(a,d) − f(b,d)`
(written `f(a,c) + f(b,d) < f(a,d) + f(b,c)` for finite values), and `(a, b) ⇝ (d, c)` otherwise;
in any case a finite-valued move `{a, b} ⇝ {c, d}`. -/
theorem lemma_4_6 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D)) (hΓ : IsLanguage Γ)
    (a b c d : D) (f : D → D → WithTop ℚ≥0) (hw : InteractionWitness Γ a b c d f) :
    (f a c + f b d < f a d + f b c → FVMove Γ a b c d) ∧
    (¬ (f a c + f b d < f a d + f b c) → FVMove Γ a b d c) ∧
    FVSetMove Γ a b c d := by sorry

end ConservativeVCSP.Treewidth
