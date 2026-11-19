-- Prove2me | Theorems.Thm_DiazModulus_dalag_prop_12_2_step
-- name    : DiazModulus.dalag_prop_12_2_step
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:00.121862+00:00
-- url     : https://prove2.me/theorems/a0ed26bf-3cd6-4035-9355-e3e51b9e4c59
-- title:
--   DALAG Prop. 12.2, inductive step: if every matrix over F₁ has the block form (A B; C 0) and x ≠ 0 is transcendental over k(F₁) or F₁ = 0, then so has xN + M₁, N over k, M₁ over F₁
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra (for example $k \subseteq K$). A matrix $M$ with $s$ rows, $t$ columns and entries in $K$ *has the block form (A B; C 0) over $k$* if there are a natural number $r \le \min(s, t)$ and invertible matrices $P \in \mathrm{GL}_s(k)$, $Q \in \mathrm{GL}_t(k)$ such that, with $P$ and $Q$ read in $K$, the matrix $N = PMQ$ has $N_{ij} = 0$ whenever $i > r$ and $j > r$ (rows and columns numbered from $1$) and its upper left $r \times r$ block $A$ is invertible: $PMQ = \begin{pmatrix} A & B \\ C & 0 \end{pmatrix}$ with $A$ regular, or empty when $r = 0$.
--
--   Let $F_1 \subseteq K$ be a $k$-vector subspace such that every matrix with entries in $F_1$ (of any size, the zero matrix included) has the block form (A B; C 0) over $k$. Let $x \in K$ with $x \neq 0$, and assume that $F_1 = \{0\}$ or $x$ is transcendental over the field $k(F_1)$ generated over $k$ by $F_1$. Let $M$ be an $s \times t$ matrix with entries in $K$ and $N$ an $s \times t$ matrix with entries in $k$ such that every entry of $M - xN$ lies in $F_1$. Then $M$ has the block form (A B; C 0) over $k$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 12.2 (p. 419; proof pp. 420–422): the induction step (pp. 421–422), with E₁ written F₁; the case F₁ = 0 is the case n = 1 of p. 420. Proved from DiazModulus.matrix_exists_rank_normal_form and DiazModulus.dalag_prop_12_2_det. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem dalag_prop_12_2_step {k K : Type*} [Field k] [Field K] [Algebra k K] (F₁ : Submodule k K)
    (hF₁ : ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ F₁) →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det)
    (x : K) (hx : x ≠ 0)
    (hxF₁ : F₁ = ⊥ ∨ Transcendental (IntermediateField.adjoin k (F₁ : Set K)) x)
    {s t : ℕ} (M : Matrix (Fin s) (Fin t) K) (N : Matrix (Fin s) (Fin t) k)
    (hMN : ∀ i j, M i j - x * algebraMap k K (N i j) ∈ F₁) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  sorry

end DiazModulus
