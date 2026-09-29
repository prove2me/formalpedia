-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_mono_of_sectionsEquiv_precomp_surjective
-- name    : AlgebraicGeometry.Scheme.mono_of_sectionsEquiv_precomp_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7c3c23d5-6fbd-5757-9bc1-b40a8dc4dd1b
-- title:
--   Surjection of Hopf algebras gives a monomorphism of points sheaves
-- statement:
--   Work on the small fppf site of $\operatorname{Spec}\mathbf Z$: the objects of `specInt.Fppf` are schemes $U$ over $\operatorname{Spec}\mathbf Z$ whose structure morphism is flat and locally of finite presentation, and the topology is `smallFppfTopology specInt`. Let $F$ and $F'$ be sheaves of abelian groups (valued in `Ab.{1}`) on this site, let $H$ and $H'$ be commutative rings equipped with Hopf algebra structures over $\mathbf Z$, and suppose given, for every object $U$, additive equivalences $e_F(U) : F(U) \simeq \operatorname{Hom}_{\mathbf Z\text{-alg}}(H, \Gamma(U,\mathcal O_U))$ and $e_{F'}(U) : F'(U) \simeq \operatorname{Hom}_{\mathbf Z\text{-alg}}(H', \Gamma(U,\mathcal O_U))$, the right-hand sides being the sets of $\mathbf Z$-algebra homomorphisms into the global sections of $U$ regarded as groups under convolution (via `WithConv`) and then written additively (via `Additive`). Let $\pi : H' \to H$ be a surjective homomorphism of $\mathbf Z$-algebras, and let $\mathrm{incl} : F \to F'$ be a morphism of sheaves such that for every $U$, every section $s \in F(U)$ and every $h' \in H'$, the algebra homomorphism attached by $e_{F'}(U)$ to $\mathrm{incl}_U(s)$ sends $h'$ to the value at $\pi(h')$ of the algebra homomorphism attached to $s$ by $e_F(U)$. Then $\mathrm{incl}$ is a monomorphism in the category of sheaves.
--
--   This is the sheaf-theoretic form of the statement that a closed immersion of affine group schemes over $\mathbf Z$, dual to a surjection of Hopf algebras, realises the functor of points of the smaller group as a subsheaf of that of the larger one on the small fppf site. It is used in the construction of the dévissage of the primary torsion of the Néron model of the Jacobian of the relevant modular curve, being cited by [`ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding) and [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_mono_of_sectionsEquiv_precomp_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem AlgebraicGeometry.Scheme.mono_of_sectionsEquiv_precomp_surjective
    (F F' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (H H' : Type) [CommRing H] [CommRing H'] [HopfAlgebra ℤ H] [HopfAlgebra ℤ H']
    (eF : ∀ U : specInt.Fppf, F.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (eF' : ∀ U : specInt.Fppf, F'.1.obj (op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (π : H' →ₐ[ℤ] H) (hπ : Function.Surjective π)
    (incl : F ⟶ F')
    (hincl : ∀ (U : specInt.Fppf) (s : F.1.obj (op U)) (h' : H'),
      (Additive.toMul (eF' U (incl.1.app (op U) s))) h' = (Additive.toMul (eF U s)) (π h')) :
    Mono incl := by sorry
