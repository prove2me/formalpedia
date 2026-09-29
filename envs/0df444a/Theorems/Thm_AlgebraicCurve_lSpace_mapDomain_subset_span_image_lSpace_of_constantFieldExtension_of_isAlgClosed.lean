-- Prove2me | Theorems.Thm_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
-- name    : AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/f2d2bd84-f499-5483-aa53-90e12e67fe5d
-- title:
--   Descent of Riemann–Roch spaces along a constant field extension
-- statement:
--   Let $K \subseteq K'$ and $F \subseteq F'$ be fields with $F/K$, $F'/K'$, $K'/K$, $F'/F$ and $F'/K$ algebras compatible in the two scalar towers $K \to K' \to F'$ and $K \to F \to F'$, with $K$ and $K'$ algebraically closed and both $F/K$ and $F'/K'$ satisfying `IsCurveOver`: every nonzero function has a divisor of degree zero recording its orders at all places, every place has residue field finite over the base field, and the module of Kähler differentials is free of rank one over the function field. Here a place is a valuation subring, different from the whole field, containing the image of the base field and a principal ideal ring, and a divisor is a finitely supported integer-valued function on places. Assume $F$ is finite over $K(x)$ for some $x$ transcendental over $K$, likewise $F'$ over $K'(x')$, and that $F'$ is generated over $K'$ by the image of $F$. Let $\mathrm{lift}$ be an injective map from places of $F/K$ to places of $F'/K'$ preserving orders, $(\mathrm{lift}\,P).\mathrm{ord}(f) = P.\mathrm{ord}(f)$ for all $f \in F$, and such that no place of $F'/K'$ outside its image pulls back along $F \to F'$ to the valuation subring of a place of $F/K$. Then for a divisor $D$ on $F/K$, every $f'$ in the Riemann–Roch space of the pushforward divisor $\mathrm{lift}_*D$, i.e. with $v'(f') \le \exp((\mathrm{lift}_*D)(v'))$ for all places $v'$ of $F'/K'$, lies in the $K'$-span of the image in $F'$ of the Riemann–Roch space of $D$.
--
--   This is the inclusion $L'(\mathrm{Con}\,D) \subseteq K' \cdot L(D)$, the substantive half of the equality $L'(\mathrm{Con}\,D) = K' \otimes_K L(D)$ for a constant field extension of function fields (Stichtenoth, Theorem 3.6.3(a)). It is used to show that the dimension $\ell(D)$ is unchanged by such an extension, that the conorm map on degree-zero divisor classes is injective, and in an estimate for hyperplane sections on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) {f' : F'}
    (hf' : f' ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) := by sorry
