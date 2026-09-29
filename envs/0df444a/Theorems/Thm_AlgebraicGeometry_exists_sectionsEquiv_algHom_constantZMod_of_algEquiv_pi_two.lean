-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
-- name    : AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/e4126592-6925-59f3-bb47-3ea108851b85
-- title:
--   Rank-two split Hopf algebra represents the constant sheaf ℤ/2
-- statement:
--   Let $K$ be a commutative ring equipped with the structure of a Hopf algebra over $\mathbb{Z}$, and suppose given an isomorphism $f : K \simeq \mathbb{Z} \times \mathbb{Z}$ of $\mathbb{Z}$-algebras (only the algebra structure of $K$ is constrained; the comultiplication is arbitrary). Then there is a family of isomorphisms of additive groups, indexed by schemes $T$ in the bottom universe,
--   $$e_T : \bigl(\mathtt{sheafULift}(\mathtt{constantZModSheaf}\ 2)\bigr)(T) \;\simeq\; \mathrm{Additive}\bigl(\mathrm{WithConv}(K \to_{\mathbb{Z}\text{-alg}} \Gamma(T,\top))\bigr),$$
--   where the left-hand side is the group of sections over $T$ of the constant fppf sheaf attached to $\mathbb{Z}/2$, namely the presheaf `continuousMapPresheafAb (ZMod 2)` of $\mathbb{Z}/2$-valued continuous functions, composed with the universe-lifting functor on abelian groups, and the right-hand side is the set of $\mathbb{Z}$-algebra homomorphisms $K \to \Gamma(T,\top)$ with the convolution multiplication coming from the Hopf structure of $K$, written additively. The family is natural: for every morphism of schemes $g : T \to T'$, every section $s$ over $T'$ and every $k \in K$, the algebra homomorphism corresponding to the restriction of $s$ along $g$ sends $k$ to the image of $(e_{T'}s)(k)$ under the ring map $\Gamma(T',\top) \to \Gamma(T,\top)$ induced by $g$. No affineness hypothesis is imposed on $T$.
--
--   This identifies the functor of points, under convolution, of a finite flat group scheme of order $2$ over $\mathbb{Z}$ whose coordinate ring splits as $\mathbb{Z} \times \mathbb{Z}$ with the constant group scheme $\mathbb{Z}/2$, in the form of an isomorphism of presheaves of abelian groups on schemes stated pointwise together with its compatibility with pullback. It is used in the analysis of the relevant fppf cohomology groups, being cited by [`ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.exists_natCard_fppfH_one_of_not_finite_of_sectionsEquiv_algHom_two) and [`ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two`](thm.html#ModularCurve.iso_restriction_or_natCard_fppfCohomology_of_sectionsEquiv_algHom_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem AlgebraicGeometry.exists_sectionsEquiv_algHom_constantZMod_of_algEquiv_pi_two
    (K : Type) [CommRing K] [HopfAlgebra ℤ K]
    (f : K ≃ₐ[ℤ] (Fin 2 → ℤ)) :
    ∃ e : ∀ T : Scheme.{0},
      ((FppfKummerSES.sheafULift.{0}.obj
          (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
        (Opposite.op T)) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(T, ⊤))),
      ∀ {T T' : Scheme.{0}} (g : T ⟶ T')
        (s : (FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.obj
          (Opposite.op T')) (k : K),
        (Additive.toMul (e T ((FppfKummerSES.sheafULift.{0}.obj
            (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} 2)).obj.map g.op s))) k
          = (Scheme.Γ.map g.op) ((Additive.toMul (e T' s)) k) := by sorry
