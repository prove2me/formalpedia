-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one
-- name    : AlgebraicCurve.Annulus.eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/a5ba3631-95f7-51f6-b4ed-93e4dcd99f27
-- title:
--   Annulus modulus exponent read off two end units at one place
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, and $F$ a field equipped with an $L$-algebra structure. Let `An` be an annulus for $A$ in $F$: a set `An.dom` of places of $F$ over $L$ (valuation subrings of $F$ containing $L$, proper and with principal ideals), a parameter `An.param` $\in F$ and a modulus `An.modulus` in the maximal ideal of $A$, subject to the annulus axioms (rationality of the places in the domain, the parameter being a nonvanishing coordinate with value in the maximal ideal there, unique realisability of admissible values, $\operatorname{ord}_P(\mathrm{param}-\mathrm{param}(P))=1$, and the unit principle). Let $p\in A$ lie in the maximal ideal with $p\neq 0$ in $L$, let $e\in\mathbb N$ and let $w\in A$ be a unit with $\mathrm{An.modulus}=p^{e}w$. Let $\zeta,\eta\in F$ and $e'\in\mathbb N$ satisfy $\zeta\eta=p^{e'}$ (image of $p^{e'}$ under $L\to F$). Suppose there is a place $P\in\mathrm{An.dom}$ with $\operatorname{ord}_P\zeta=\operatorname{ord}_P\eta=0$ such that $\zeta(P)\cdot\mathrm{param}(P)^{-1}$ lies in $A$ and is a unit of $A$, and likewise $\eta(P)\cdot\bigl((\mathrm{modulus}\cdot\mathrm{param}^{-1})(P)\bigr)^{-1}$ lies in $A$ and is a unit of $A$, where $f(P)$ denotes the evaluation `P.evalAt f` of $f$ at $P$, taken in $L$ via the residue field. Then $e'=e$.
--
--   This is the width-matching step for an annulus: the exponent $e$ in a factorisation $\mathrm{modulus}=p^{e}w$ of the modulus is pinned down by the existence of a single place of the annulus at which two functions with product $p^{e'}$ satisfy the two end-slope laws at exponent one, one relative to the parameter and one relative to the flipped parameter $\mathrm{modulus}/\mathrm{param}$. It is used in the analysis of sections of the model of the modular curve at $p$ near a crossing, where divisibility of the width by the relevant exponent is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.Annulus.eq_of_mul_eq_algebraMap_pow_of_isUnit_evalAt_mul_evalAt_param_zpow_neg_one
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (p : ↥A) (hp : p ∈ maximalIdeal ↥A) (hp0 : (p : L) ≠ 0)
    (e : ℕ) (w : ↥A) (hw : IsUnit w) (hmod : An.modulus = p ^ e * w)
    (ζ η : F) (e' : ℕ) (hζη : ζ * η = algebraMap L F ((p : L) ^ e'))
    (P : Place L F) (hP : P ∈ An.dom) (hζ0 : P.ord ζ = 0) (hη0 : P.ord η = 0)
    (hζ : ∃ h : P.evalAt ζ * (P.evalAt An.param) ^ (-(1 : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hη : ∃ h : P.evalAt η * (P.evalAt (algebraMap L F ((An.modulus : ↥A) : L) * An.param⁻¹)) ^ (-(1 : ℤ)) ∈ A,
      IsUnit (⟨_, h⟩ : ↥A)) :
    e' = e := by sorry
