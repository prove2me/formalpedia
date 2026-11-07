-- Prove2me | Theorems.Thm_ConsModCount_unweighted_binary_obstruction
-- name    : ConsModCount.unweighted_binary_obstruction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:16.381103+00:00
-- url     : https://prove2.me/theorems/910f57be-90fe-4c5d-925e-cc58a2fe1635
-- title:
--   Lemma (Unweighted binary obstruction) — a positive nonsingular $2\times2$ count matrix
-- statement:
--   Let $H$ be a finite template on a finite nonempty set $D$ containing every unary subset. If $H$ has a Mal'tsev polymorphism and is not strongly balanced, there is an unweighted $H$-gadget with two distinct ports $x,y$ such that
--
--   1. its integer extension-count matrix $(a,b)\mapsto\mathrm{ext}(a,b)$ on $D\times D$ is not block-rank-one;
--   2. there are $a_0\ne a_1$ and $b_0\ne b_1$ in $D$ with all four counts $\mathrm{ext}(a_i,b_j)$ positive and
--
--   $$\mathrm{ext}(a_0,b_0)\,\mathrm{ext}(a_1,b_1)\ne\mathrm{ext}(a_0,b_1)\,\mathrm{ext}(a_1,b_0).$$
--
--   The sets $\{a_0,a_1\}$ and $\{b_0,b_1\}$ need not be equal or disjoint. This is the first step of the extraction of $Q_C$.
--
--   Differences from the source:
--   - encoding: after adding unary predicates A(x), B(y) to the terminals, the resulting 2 × 2 count matrix is positive and nonsingular → the four entries of the gadget's count matrix at (a_i, b_j) are positive with nonzero determinant; reason: adding the unary constraints leaves the counts on A × B unchanged, and the predicates exist by conservativity
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §10.1, Lemma (Unweighted binary obstruction), p.15 (PDF p.16)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Unweighted binary obstruction)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §10.1, p.15, PDF p.16). Under the standing
assumption of §§10–13 (`H` conservative): if `H` has a Mal'tsev polymorphism and is not strongly
balanced, then there is a finite unweighted `H`-gadget with two distinct exposed variables `x, y`
whose integer extension-count matrix is not block-rank-one. After adding unary predicates to these
terminals, their domains may be taken to be two-element sets `A = {a₀, a₁}`, `B = {b₀, b₁}`, and
the resulting `2 × 2` count matrix is positive and nonsingular over the integers. `A` and `B` need
not be equal or disjoint.

**Formalization Note.** Adding the unary predicates `A(x)`, `B(y)` (available by conservativity)
leaves the counts on `A × B` unchanged, so the `2 × 2` matrix is stated as the entries of the
gadget's count matrix at `(aᵢ, bⱼ)`. -/
theorem unweighted_binary_obstruction {D : Type} [Fintype D] [DecidableEq D] [Nonempty D] (H : Template D)
    (hH : Conservative H) (hM : HasMaltsev H) (hSB : ¬ StronglyBalanced H) :
    ∃ G : Gadget H 2, G.port 0 ≠ G.port 1 ∧
      ¬ BlockRankOne (fun a b : D => G.extCount ![a, b]) ∧
      ∃ a₀ a₁ b₀ b₁ : D, a₀ ≠ a₁ ∧ b₀ ≠ b₁ ∧
        0 < G.extCount ![a₀, b₀] ∧ 0 < G.extCount ![a₀, b₁] ∧
        0 < G.extCount ![a₁, b₀] ∧ 0 < G.extCount ![a₁, b₁] ∧
        ((G.extCount ![a₀, b₀] : ℤ) * G.extCount ![a₁, b₁] ≠
          (G.extCount ![a₀, b₁] : ℤ) * G.extCount ![a₁, b₀]) := by sorry

end ConsModCount
