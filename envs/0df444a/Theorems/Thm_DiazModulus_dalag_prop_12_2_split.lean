-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_2_split
-- name    : DiazModulus.dalag_prop_12_2_split
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:01.804092+00:00
-- url     : https://prove2.me/theorems/d3fbc770-9ed7-4717-aee7-6dbb146bbde9
-- title:
--   Under (ii) of DALAG Prop. 12.13, a non-zero finite-dimensional k-subspace F ⊆ E is F₁ ⊕ kx with x ≠ 0 and either F₁ = 0 or x transcendental over k(F₁)
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). Let $E \subseteq K$ be a $k$-vector subspace satisfying condition (ii) of DALAG Prop. 12.13: whenever $x_1, \dots, x_n \in E$ ($n \ge 0$) and $1, x_1, \dots, x_n$ are linearly independent over $k$, the elements $x_1, \dots, x_n$ are algebraically independent over $k$.
--
--   Let $F \subseteq E$ be a non-zero finite-dimensional $k$-vector subspace. Then there are $x \in F$ with $x \neq 0$ and a $k$-vector subspace $F_1 \subsetneq F$ such that every $f \in F$ satisfies $f - cx \in F_1$ for some $c \in k$ (so $F = F_1 \oplus kx$), and either $F_1 = \{0\}$ or $x$ is transcendental over the field $k(F_1)$ generated over $k$ by $F_1$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.2 (p. 419; proof pp. 420–422): the choice of x and of E₁ with E₀ = E₁ ⊕ kx (p. 421), and the analogue of Lemma 12.3, (ii) ⇒ (iii) (p. 420), which makes x transcendental over k(E₁) (p. 422). Here E is any subspace with property (ii) of Prop. 12.13, and x is a member other than 1 of a k-basis of k·1 + F that contains 1, so that F₁ contains 1 when 1 ∈ F and F ≠ k·1; for k + E₀ the printed step "x ∉ E₁, hence x is transcendental over k(E₁)" fails whenever 1 lies in the span of the entries but not in E₁. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_2_split {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x)
    (F : Submodule k K) [FiniteDimensional k ↥F] (hFE : F ≤ E) (hF : F ≠ ⊥) :
    ∃ (x : K) (F₁ : Submodule k K), x ∈ F ∧ x ≠ 0 ∧ F₁ < F ∧
      (∀ f ∈ F, ∃ c : k, f - x * algebraMap k K c ∈ F₁) ∧
      (F₁ = ⊥ ∨ Transcendental (IntermediateField.adjoin k (F₁ : Set K)) x) := by
  sorry

end DiazModulus
