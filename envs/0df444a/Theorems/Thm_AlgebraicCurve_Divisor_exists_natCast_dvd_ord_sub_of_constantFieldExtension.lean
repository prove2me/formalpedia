-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension
-- name    : AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/480b8437-a006-5205-aadf-6aea62dbcce9
-- title:
--   Descent of n-divisibility of divisor classes along constant-field extension
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with compatible algebra structures making $K \to K' \to F'$ and $K \to F \to F'$ towers, with $K$ algebraically closed of characteristic zero and $K'$ algebraically closed. Assume (`hfg`) there is $x \in F$ transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and likewise (`hfg'`) some $x \in F'$ transcendental over $K'$ with $F'$ finite over $K'(x)$; assume `IsCurveOver K F` and `IsCurveOver K' F'`, i.e. for each of the two extensions: every nonzero element has a finitely supported divisor of degree $0$ recording its orders at all places, every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank one; and assume (`hgen`) that $K'$ adjoined to the image of $F$ in $F'$ is all of $F'$. Here a place of $F/K$ is a valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $K$ whose underlying ring is a principal ideal ring, $v.\mathrm{ord}$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $n$ be a nonzero natural number, $D$ a divisor of $F/K$ and $D'$ a divisor of $F'/K'$ such that $D'(v') = D(v)$ whenever $\mathcal{O}_{v'}$ pulls back along $F \to F'$ to $\mathcal{O}_v$ (`hD'over`), and $D'(v') = 0$ when the pullback of $\mathcal{O}_{v'}$ is the valuation subring of no place of $F/K$ (`hD'off`). If there is a nonzero $f' \in F'$ with $n \mid \mathrm{ord}_{v'}(f') - D'(v')$ for every place $v'$ of $F'/K'$, then there is a nonzero $f \in F$ with $n \mid \mathrm{ord}_v(f) - D(v)$ for every place $v$ of $F/K$.
--
--   The statement says that $n$-divisibility of a divisor class in the Picard group of a curve over an algebraically closed field of characteristic zero is insensitive to enlarging the constant field to a larger algebraically closed field, the divisor upstairs being the conorm of the one downstairs (described here by its values rather than constructed). It is used to descend divisibility statements for differences of points, via [`AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single`](thm.html#AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single), and in the divisibility input to the treatment of the modular curve of level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hdiv' : ∃ f' : F', f' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) ∣ v'.ord f' - D' v') :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) ∣ v.ord f - D v := by sorry
