-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
-- name    : AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/169deea7-58da-5bd1-9e8c-b2e1262b9416
-- title:
--   Rational places are unramified in separable Kummer extensions
-- statement:
--   Let $K$, $F$, $L$ be fields with $F$ and $L$ algebras over $K$ and $L$ an algebra over $F$, compatibly (scalar tower), with $L/F$ finite and separable, and let $p$ be a prime. Let $f \in F$ and $\alpha \in L$ satisfy: $f$ is not a $p$-th power in $F$ (no $g \in F$ has $g^p = f$), $\alpha^p$ is the image of $f$ in $L$, and $F\langle\alpha\rangle = \top$, i.e. $\alpha$ generates $L$ over $F$. Here a place of a $K$-algebra field is a valuation subring containing the image of $K$, different from the whole field, and a principal ideal ring; $\mathrm{ord}$ denotes minus the logarithm of the associated adic valuation. Assume that $p$ divides $\mathrm{ord}_v(f)$ in $\mathbb{Z}$ for every place $v$ of $F$ over $K$. Then for every place $w$ of $L$ over $K$ which is rational, in the sense that the structure map from $K$ to the residue field of $w$ is surjective, the ramification index $e(w \mid F)$ equals $1$; by definition this index is the least positive integer $n$ of the form $\mathrm{ord}_w(\iota(g))$ for some nonzero $g \in F$, $\iota : F \to L$ the structure map, so the assertion is that some nonzero element of $F$ has image of order exactly $1$ at $w$.
--
--   This is the tameness statement for a degree-$p$ Kummer cover $L = F(f^{1/p})$ whose radicand has order divisible by $p$ at every place: such a cover is unramified at all rational places, the separability hypothesis replacing any restriction on the characteristic. It feeds the Riemann–Hurwitz style genus computation [`AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero`](thm.html#AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord_of_natCast_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord_of_isSeparable {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {p : ℕ} [Fact p.Prime] {f : F} {α : L}
    (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤)
    (hord : ∀ v : Place K F, (p : ℤ) ∣ v.ord f)
    (w : Place K L) (hw_rat : w.IsRational) :
    w.ramificationIndex F = 1 := by sorry
