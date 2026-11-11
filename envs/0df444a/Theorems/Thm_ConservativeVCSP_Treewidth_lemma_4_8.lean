-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_lemma_4_8
-- name    : ConservativeVCSP.Treewidth.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:47:44.767198+00:00
-- url     : https://prove2.me/theorems/110284a0-14bd-4afa-9c04-71f8b049ab6a
-- title:
--   Lemma 4.8 — transferring costs from a pair to products of sets
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a constraint language over $D$, $P=\{p,q\}\subseteq D$ with $p\ne q$, $r\ge1$ and $S_1,\dots,S_r\subseteq D$ nonempty. Suppose $\Gamma$ expresses all finite-valued cost functions on $P$, all finite-valued unary cost functions on each $S_i$, and a restriction to $P$, and that there is a finite-valued move $\{a,b\}\rightsquigarrow P$ for all distinct $a,b\in S_i$, for each $i$. Then for every $f:S_1\times\cdots\times S_r\to\mathbb Q_{\ge0}$ there are a finite-valued $g\in\mathrm{pow}(\Gamma)$ and $c\in\mathbb Q$ with
--   $$g(\bar x)=f(\bar x)+c\qquad(\bar x\in S_1\times\cdots\times S_r).$$
--
--   It moves the expressive power available on one pair to larger sets connected to it by moves.
--
--   Differences from the source:
--   - encoding: $f : S_1\times\cdots\times S_r\to\mathbb Q_{\ge0}$ → `f : ((i : Fin r) → S i) → ℚ≥0`, and `g` of arity `r` with `toQ (g x) = f x + c` on the product (`ExpressesOn`); reason: Lean convention for a product of subsets
--   - encoding: cost values in $\mathbb{Q}_{\ge 0}\cup\{\infty\}$, additive shifts $c\in\mathbb{Q}$ → `WithTop ℚ≥0`; a shift is applied after the inclusion `toQ` into `WithTop ℚ` (with ∞ + c = ∞); reason: Lean convention; the same functions and the same shifts
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 22, Lemma 4.8

import Definitions.Def_ConservativeVCSP_Treewidth_Moves

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Lemma 4.8 (Transferring costs to sets, p. 22): with all finite-valued cost functions on
`P = {p, q}`, all finite-valued unary cost functions on each nonempty `S_i`, a restriction to `P`,
and a finite-valued move `{a, b} ⇝ P` for all distinct `a, b ∈ S_i`, every
`f : S₁ × ⋯ × S_r → ℚ≥0` (`r ≥ 1`) is a finite-valued member of `pow(Γ)` up to a constant. -/
theorem lemma_4_8 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D)) (hΓ : IsLanguage Γ)
    (p q : D) (hpq : p ≠ q) (r : ℕ) (hr : 1 ≤ r) (S : Fin r → Set D)
    (hS : ∀ i, (S i).Nonempty)
    (hP : ExpressesAllFV Γ {p, q})
    (hunary : ∀ i, ExpressesAllUnaryFV Γ (S i))
    (hres : ExpressesRestriction Γ {p, q})
    (hmove : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a ≠ b → FVSetMove Γ a b p q) :
    ∀ f : ((i : Fin r) → S i) → ℚ≥0, ExpressesOn Γ S f := by sorry

end ConservativeVCSP.Treewidth
