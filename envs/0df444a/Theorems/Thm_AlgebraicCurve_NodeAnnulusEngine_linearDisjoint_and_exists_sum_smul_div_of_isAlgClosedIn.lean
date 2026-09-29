-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
-- name    : AlgebraicCurve.NodeAnnulusEngine.linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/ca7c531b-fda6-5c05-a52d-25dd3ef8f8a0
-- title:
--   Linear disjointness over C and L-generation of F
-- statement:
--   Let $k$ be a field of characteristic zero, $L$ a field extension of $k$, and $F$ a field extension of $L$ which is also a $k$-algebra compatibly (scalar tower $k \subseteq L \subseteq F$). Let $K$ be a $k$-intermediate field of $L$ such that every element of $L$ is algebraic over $K$, and let $FK$ be a $k$-intermediate field of $F$ whose image contains the image of $K$ under $L \to F$. Assume: (generation) every $f \in F$ satisfies $f \cdot \sum_{j} d_j \cdot b_j = \sum_i c_i \cdot a_i$ for some finite families $c_i, d_j \in L$ and $a_i, b_j \in FK$ with $\sum_j d_j \cdot b_j \neq 0$; (regularity) every $x \in FK$ annihilated by the image in $F$ of some nonzero polynomial over $L$ all of whose coefficients lie in $K$ is the image of an element of $K$. Let $C$ be a subring of $L$ contained in $K$ such that every $y \in K$ satisfies $y d = c$ with $c, d \in C$, $d \neq 0$, and let $\mathcal{N}_0$ be a subring of $F$ contained in $FK$ such that every $x \in FK$ satisfies $x b = a$ with $a, b \in \mathcal{N}_0$, $b \neq 0$. The conclusion is twofold: (i) for every finite family $c : \mathrm{Fin}\, n \to L$ that is linearly independent over $C$ and every $a : \mathrm{Fin}\, n \to \mathcal{N}_0$, the relation $\sum_i c_i \cdot a_i = 0$ in $F$ forces $a_i = 0$ for all $i$; and (ii) every $f \in F$ admits $c_i \in L$, $a_i \in \mathcal{N}_0$ and $b \in \mathcal{N}_0$ with $b \neq 0$ and $f b = \sum_i c_i \cdot a_i$.
--
--   This is the field-theoretic statement that a regular extension is linearly disjoint from any algebraic extension of its field of constants, together with the corresponding denominator-clearing generation statement, in the form of the linear disjointness over $C$ and $L$-generation hypotheses of the node-annulus machinery. It is used in the proof of [`IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver`](thm.html#IntermediateField.finiteDimensional_adjoin_and_isSeparable_of_form_of_isAlgebraic_of_isCurveOver), where $K$ is a number field and $\mathcal{N}_0$ a ring built from the $K$-form of a function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.NodeAnnulusEngine.linearDisjoint_and_exists_sum_smul_div_of_isAlgClosedIn
    {k : Type*} [Field k] [CharZero k] {L : Type*} [Field L] [Algebra k L] {F : Type*} [Field F] [Algebra L F] [Algebra k F]
    [IsScalarTower k L F]
    (K : IntermediateField k L) (halg : ∀ y : L, IsAlgebraic ↥K y)
    (FK : IntermediateField k F)
    (hKFK : ∀ y : L, y ∈ K → algebraMap L F y ∈ FK)
    (hgenF : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → F) (m : ℕ) (d : Fin m → L) (b : Fin m → F),
      (∀ i, a i ∈ FK) ∧ (∀ j, b j ∈ FK) ∧ (∑ j, d j • b j) ≠ 0 ∧ f * (∑ j, d j • b j) = ∑ i, c i • a i)

    (hreg : ∀ x : F, x ∈ FK → (∃ p : Polynomial L, p ≠ 0 ∧ (∀ i, p.coeff i ∈ (K : Set L)) ∧
        Polynomial.aeval x (p.map (algebraMap L F)) = 0) → ∃ y : L, y ∈ K ∧ x = algebraMap L F y)
    (C : Subring L) (hCK : ∀ c : L, c ∈ C → c ∈ K)
    (hCfrac : ∀ y : L, y ∈ K → ∃ c d : L, c ∈ C ∧ d ∈ C ∧ d ≠ 0 ∧ y * d = c)
    (𝒩₀ : Subring F) (h𝒩₀ : ∀ a : F, a ∈ 𝒩₀ → a ∈ FK)
    (h𝒩₀frac : ∀ x : F, x ∈ FK → ∃ a b : F, a ∈ 𝒩₀ ∧ b ∈ 𝒩₀ ∧ b ≠ 0 ∧ x * b = a) :
    (∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0) ∧
    (∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F)) := by sorry
