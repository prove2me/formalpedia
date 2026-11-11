-- Prove2me | Theorems.Thm_ConservativeVCSP_Treewidth_lemma_6_4
-- name    : ConservativeVCSP.Treewidth.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:47:52.432644+00:00
-- url     : https://prove2.me/theorems/cdd34824-071e-4122-8fb4-64b9a7fbd9ab
-- title:
--   Lemma 6.4 — reduction to binary functions
-- statement:
--   Let $D$ be a finite domain, $\Gamma$ a finite-valued hard-list language over $D$, and $g\in\mathrm{pow}(\Gamma)$ finite-valued of arity $m$. Let $S,T$ be a partition of $[m]$ and $\bar x,\bar y\in D^m$ with
--   $$g(\bar x)+g(\bar y)<g(\bar x_S\cdot\bar y_T)+g(\bar y_S\cdot\bar x_T).$$
--   Then there are $i\in S$, $j\in T$ with $x_i\ne y_i$, $x_j\ne y_j$ and a finite-valued binary $h\in\mathrm{pow}(\Gamma)$ with $h(x_i,x_j)+h(y_i,y_j)<h(x_i,y_j)+h(y_i,x_j)$. The same holds with both inequalities reversed.
--
--   It reduces a failure of modularity of an arbitrary expressed function to a binary one, which is what interaction speaks about.
--
--   Differences from the source:
--   - encoding: a partition $S,T$ of $[m]$ and $\bar x_S\cdot\bar y_T$ → `S : Finset (Fin m)`, `T` its complement (0-based positions), `mixTuple S x y`; reason: Lean convention; empty parts make the hypothesis false in the source too
--   - encoding: 'the same holds with both inequalities reversed' → a second conjunct with both strict inequalities reversed; reason: literal rendering
--   - encoding: cost values in $\mathbb{Q}_{\ge 0}\cup\{\infty\}$, additive shifts $c\in\mathbb{Q}$ → `WithTop ℚ≥0`; a shift is applied after the inclusion `toQ` into `WithTop ℚ` (with ∞ + c = ∞); reason: Lean convention; the same functions and the same shifts
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 32, Lemma 6.4

import Definitions.Def_ConservativeVCSP_Treewidth_Moves

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- Lemma 6.4 (Reduction to binary functions, p. 32): for a finite-valued `g ∈ pow(Γ)` of arity
`m`, a partition `S, T` of `[m]` and `x̄, ȳ ∈ D^m` with
`g(x̄) + g(ȳ) < g(x̄_S · ȳ_T) + g(ȳ_S · x̄_T)`, there are `i ∈ S`, `j ∈ T` with `x_i ≠ y_i`,
`x_j ≠ y_j` and a finite-valued binary `h ∈ pow(Γ)` with
`h(x_i, x_j) + h(y_i, y_j) < h(x_i, y_j) + h(y_i, x_j)`; the same with both inequalities
reversed. -/
theorem lemma_6_4 {D : Type} [Fintype D] [Nonempty D] (Γ : Set (CostFn D))
    (hΓ : IsFVHardListLanguage Γ) (m : ℕ) (g : (Fin m → D) → WithTop ℚ≥0)
    (hg : InPow Γ ⟨m, g⟩) (hfin : ∀ x, g x ≠ ⊤) (S : Finset (Fin m)) (x y : Fin m → D) :
    (g x + g y < g (mixTuple S x y) + g (mixTuple S y x) →
      ∃ i ∈ S, ∃ j ∉ S, x i ≠ y i ∧ x j ≠ y j ∧
        ∃ h : D → D → WithTop ℚ≥0, (∀ s t, h s t ≠ ⊤) ∧ InPow Γ (binary h) ∧
          h (x i) (x j) + h (y i) (y j) < h (x i) (y j) + h (y i) (x j)) ∧
    (g (mixTuple S x y) + g (mixTuple S y x) < g x + g y →
      ∃ i ∈ S, ∃ j ∉ S, x i ≠ y i ∧ x j ≠ y j ∧
        ∃ h : D → D → WithTop ℚ≥0, (∀ s t, h s t ≠ ⊤) ∧ InPow Γ (binary h) ∧
          h (x i) (y j) + h (y i) (x j) < h (x i) (x j) + h (y i) (y j)) := by sorry

end ConservativeVCSP.Treewidth
