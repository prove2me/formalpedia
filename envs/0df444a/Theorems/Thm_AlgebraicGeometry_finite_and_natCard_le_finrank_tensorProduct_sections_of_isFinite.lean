-- Prove2me | Theorems.Thm_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
-- name    : AlgebraicGeometry.finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b8c39e50-2106-5cbc-acd4-7b3bd7f583a0
-- title:
--   Bounding Ω-points of a finite part by the special fibre's rank
-- statement:
--   Let $R$ be a commutative local ring, let $X$ and $X^{f}$ be schemes, and let $g : X \to \operatorname{Spec} R$ and $i : X^{f} \to X$ be morphisms such that the composite $i$ followed by $g$ is a finite morphism. Let $\Omega$ be a field equipped with an $R$-algebra structure. Consider the set of morphisms $x : \operatorname{Spec}\Omega \to X^{f}$ whose composite with $i$ followed by $g$ equals the morphism $\operatorname{Spec}\Omega \to \operatorname{Spec} R$ induced by the structure map $R \to \Omega$, i.e. the set of $\Omega$-valued points of $X^{f}$ over $R$. The assertion is twofold: first, this set is finite; second, when the ring of global sections $\Gamma(X^{f},\top)$ is given the $R$-algebra structure coming from the ring homomorphism obtained by composing the inverse of the isomorphism $R \cong \Gamma(\operatorname{Spec} R,\top)$ with the map on global sections induced by $i$ followed by $g$, the $R$-module $\Gamma(X^{f},\top)$ is module-finite, and the cardinality of that set of points is at most the dimension, over the residue field $\kappa$ of $R$, of $\kappa \otimes_R \Gamma(X^{f},\top)$.
--
--   This is the scheme-theoretic form of the bound '$\#X^{f}(\Omega)_R \le \dim_\kappa(\kappa \otimes_R B)$' for a finite part $X^{f}$ of an $R$-scheme, with $B$ its ring of global sections; it is the geometric counterpart of the algebraic bound on the number of $R$-algebra maps from a module-finite algebra into a field. It is used to obtain finiteness and cardinality estimates for points of special fibres, in particular for torsion subsets on Néron models of modular Jacobians arising in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.finite_and_natCard_le_finrank_tensorProduct_sections_of_isFinite
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X Xf : Scheme.{u}} (g : X ⟶ Spec (.of R)) (i : Xf ⟶ X) [IsFinite (i ≫ g)]
    (Ω : Type u) [Field Ω] [Algebra R Ω] :
    Finite {x : Spec (.of Ω) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))} ∧
    (letI : Algebra R Γ(Xf, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ g).appTop).hom.toAlgebra
     Module.Finite R Γ(Xf, ⊤) ∧
     Nat.card {x : Spec (.of Ω) ⟶ Xf // x ≫ i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Ω))} ≤
       Module.finrank (IsLocalRing.ResidueField R)
         (TensorProduct R (IsLocalRing.ResidueField R) Γ(Xf, ⊤))) := by sorry
