-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add
-- name    : AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/b42fd251-f59f-56ad-9044-a7f5afcdaec1
-- title:
--   Two-component local exchange identity for e and f
-- statement:
--   Let $K \subseteq F$ and let $F_1, F_2, Z, Z'$ be fields, with $F_1$, $F_2$ algebras over $F$ and $Z$, $Z'$ algebras over each of $F$, $F_1$, $F_2$, all the relevant scalar towers over $K$ and over $F$ being compatible; assume $F_1$ and $F_2$ are finite over $F$, that $Z$ and $Z'$ are finite over both $F_1$ and $F_2$, and that $F$ has characteristic zero. Assume moreover that $Z$ is generated as an $F$-algebra by the images of $F_1$ and $F_2$, that the same holds for $Z'$, that $[Z:F_1] + [Z':F_1] = [F_2:F]$, and that there are $a \in F_2$ and $b \in F_1$ whose images agree in $Z'$ but differ in $Z$. Let $w_1$ and $w_2$ be places of $F_1$ and of $F_2$ over $K$ — that is, valuation subrings, containing the image of $K$, proper, and principal ideal rings — whose contractions along $F \to F_1$ and $F \to F_2$ coincide. Let $T$ be a finite set of places of $Z$ consisting exactly of those $W$ contracting to $w_1$ on $F_1$ and to $w_2$ on $F_2$, and let $T'$ be the corresponding finite set of places of $Z'$. Then, with $e(W \mid F_1)$ the least positive $n$ that is the order at $W$ of the image of some nonzero element of $F_1$, and $f(W \mid F_2)$ the degree of the residue field of $W$ over the residue field of its contraction to $F_2$, one has the equality of natural numbers $$\sum_{W \in T} e(W \mid F_1)\, f(W \mid F_2) + \sum_{W \in T'} e(W \mid F_1)\, f(W \mid F_2) = f(w_1 \mid F)\, e(w_2 \mid F).$$
--
--   This is the place-level form of the base-change (Mackey) identity for a fibre product that splits into two components, the hypotheses $[Z:F_1]+[Z':F_1]=[F_2:F]$ together with the generation and separation conditions expressing that $F_1 \otimes_F F_2$ decomposes as $Z \times Z'$. It is used to prove [`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top`](thm.html#AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top), the divisor-theoretic comparison of a pullback of a pushforward with the sum of the two component contributions, which underlies relations of the shape $\beta^*\alpha_* = U_p + w_{p*}$ on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add.lean

import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [Algebra F F₁] [Algebra F F₂] [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z']
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F Z] [IsScalarTower K F Z']
    [IsScalarTower K F₁ Z] [IsScalarTower K F₂ Z] [IsScalarTower K F₁ Z'] [IsScalarTower K F₂ Z']
    [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₂ Z] [FiniteDimensional F₁ Z'] [FiniteDimensional F₂ Z']
    [CharZero F]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (w₁ : Place K F₁) (w₂ : Place K F₂) (hw : w₁.restrict F = w₂.restrict F)
    (T : Finset (Place K Z)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂)
    (T' : Finset (Place K Z')) (hT' : ∀ W, W ∈ T' ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
        + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F := by sorry
