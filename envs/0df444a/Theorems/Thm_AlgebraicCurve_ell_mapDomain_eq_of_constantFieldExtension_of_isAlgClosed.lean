-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/85b5f1e2-5144-57bd-914d-4779dc077cdf
-- title:
--   Invariance of ℓ(D) under constant field extension
-- statement:
--   Let $K \subseteq K'$ and $F, F'$ be fields with $F$ a $K$-algebra, $F'$ a $K'$-algebra and an $F$-algebra, compatibly in the sense that $K \to K' \to F'$ and $K \to F \to F'$ both compose to the given $K$-algebra structure on $F'$, and assume $K$ and $K'$ algebraically closed. Assume $F$ is finitely generated of transcendence degree one over $K$, in the form: some $x \in F$ is transcendental over $K$ with $F$ finite-dimensional over $K(x)$, and likewise for $F'$ over $K'$; assume also `IsCurveOver K F` and `IsCurveOver K' F'`, i.e. every nonzero function has a principal divisor of degree $0$, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field. Assume $F'$ is generated over $K'$ by the image of $F$, i.e. the intermediate field $K'$ adjoined to $\mathrm{range}(F \to F')$ is all of $F'$. Here a place of $F/K$ is a valuation subring of $F$ containing $K$, distinct from $F$, whose ring is a principal ideal ring, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, and $\ell(D) = \dim_K \{f \in F : v(f) \le \exp(D(v)) \text{ for all } v\}$ for the $\mathbb{Z}^{m0}$-valued adic valuations $v$. Let $\mathrm{lift}$ be an injective map from places of $F/K$ to places of $F'/K'$ such that $\mathrm{ord}_{\mathrm{lift}(P)}(f) = \mathrm{ord}_P(f)$ for all $f \in F$, and such that every place $v'$ of $F'/K'$ outside the image of $\mathrm{lift}$ has $v'$ pulled back along $F \to F'$ different from every place of $F/K$. Then for every divisor $D$ of $F/K$ whose Riemann–Roch space is finite-dimensional over $K$, the pushforward `D.mapDomain lift` satisfies $\ell_{K'}(\mathrm{mapDomain}\,\mathrm{lift}\,D) = \ell_K(D)$.
--
--   This is the invariance of the Riemann–Roch dimension under a constant field extension with algebraically closed base field (Stichtenoth, Theorem 3.6.3(a)), the divisor being transported by the given lifting of places. It is used to compare genera across the extension, in the two inequalities [`AlgebraicCurve.genusFF_le_of_constantFieldExtension_of_isAlgClosed`](thm.html#AlgebraicCurve.genusFF_le_of_constantFieldExtension_of_isAlgClosed) and [`AlgebraicCurve.le_genusFF_of_constantFieldExtension_of_isAlgClosed`](thm.html#AlgebraicCurve.le_genusFF_of_constantFieldExtension_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) [FiniteDimensional K ↥(riemannRochSpace D)] :
    ell (K := K') (D.mapDomain lift) = ell (K := K) D := by sorry
