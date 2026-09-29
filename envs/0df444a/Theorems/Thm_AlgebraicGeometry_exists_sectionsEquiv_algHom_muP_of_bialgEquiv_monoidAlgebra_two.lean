-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
-- name    : AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/fd252727-8ea2-51c2-8545-2038f91467b1
-- title:
--   ℤ[ℤ/2] represents the fppf sheaf μ₂
-- statement:
--   Let $K$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}$, and let $f$ be an isomorphism of $\mathbb{Z}$-bialgebras $K \simeq \mathbb{Z}[\mathrm{Multiplicative}(\mathbb{Z}/2)]$, the monoid algebra of the multiplicative group $\mathbb{Z}/2$. The conclusion asserts the existence of a family $e$ indexed by all schemes $T$ (in the bottom universe) of isomorphisms of additive groups between the sections over $T$ of the sheaf [`FppfKummerSES.muPAbelianSheafLifted 2`](def/AlgebraicGeometry_FppfKummerProp17.html#L608), that is, the value at $\mathrm{op}\,T$ of the underlying presheaf of the kernel of the $2$-power endomorphism `gmPowSelf 2` of the universe-lifted fppf abelian sheaf $\mathbb{G}_m$, and the group $\mathrm{Hom}_{\mathbb{Z}\text{-}\mathrm{alg}}(K, \Gamma(T,\top))$ of $\mathbb{Z}$-algebra homomorphisms from $K$ into the global sections of $T$, equipped with the convolution multiplication (`WithConv`) and viewed additively. The family is required to be natural in the following explicit form: for every morphism of schemes $g : T \to T'$, every section $s$ over $T'$ and every $k \in K$, the homomorphism attached by $e$ to the restriction of $s$ along $g$ sends $k$ to $\Gamma(g)$ applied to the value at $k$ of the homomorphism attached to $s$.
--
--   This is the Oort–Tate style identification of the fppf sheaf $\mu_2$, presented as the kernel of squaring on $\mathbb{G}_m$, with the functor of $\mathbb{Z}$-algebra points of the group algebra $\mathbb{Z}[\mathbb{Z}/2]$ under convolution, stated here for arbitrary schemes $T$ via global sections rather than only for affine ones. It is used in the study of the $2$-torsion of the relevant modular curves, in [`ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two) and [`ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐc[ℤ] MonoidAlgebra ℤ (Multiplicative (ZMod 2))) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T)) ≃+
        Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.obj (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.muPAbelianSheafLifted.{0} 2).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by sorry
