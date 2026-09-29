-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor
-- name    : AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_mul_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5ebe8cfd-ad51-588e-957e-dadbc0e94b3a
-- title:
--   Theorem of the square for slices of the Mumford bundle
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f' = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} k$, compatible with base change in $T$; assume $L$ is commutative (`IsCommutative`), and assume `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathcal L$ be an object of $A$-modules which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module on $U$. Write $\Lambda(\mathcal L) = \mu^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ for the Mumford bundle on $A \times_{\operatorname{Spec} k} A$, where $\mu$ is the multiplication morphism attached to $L$, $p_1,p_2$ are the projections and $\mathcal L^\vee$ is the internal hom from $\mathcal L$ to the unit. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} k$, and let $x, y$ be $\operatorname{Spec} R$-points of $A$ over $t$; for such a point $z$ let $\mathrm{sliceAt}\,z : A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to A \times_{\operatorname{Spec} k} A$ be $(p_1, z \circ p_2)$. Then the modules $(\mathrm{sliceAt}(L.\mathrm{mul}\,t\,x\,y))^*\Lambda(\mathcal L)$ and $(\mathrm{sliceAt}\,x)^*\Lambda(\mathcal L) \otimes (\mathrm{sliceAt}\,y)^*\Lambda(\mathcal L)$ are locally isomorphic over the base: for every point $s$ of $\operatorname{Spec} R$ there is an open $U \ni s$ such that the two modules become isomorphic after pullback along the inclusion of the preimage of $U$ under the projection $A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to \operatorname{Spec} R$.
--
--   This is the theorem of the square in families: the assignment $z \mapsto (\mathrm{sliceAt}\,z)^*\Lambda(\mathcal L)$ is additive in the point $z$, though only locally on $\operatorname{Spec} R$, since the discrepancy is the pullback of a line bundle from the base. It is the input for the statements that the stabiliser of $\mathcal L$ is a subgroup functor and that this stabiliser consists of two-torsion points, and for the corresponding computation with the inverse point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_sliceAt_mumfordBundle_mul_tensor.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.locIsoOnBase_sliceAt_mumfordBundle_mul_tensor
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f (L.mul t x y))).obj (mumfordBundle f L 𝓛)) ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ⊗ (Scheme.Modules.pullback (sliceAt f y)).obj (mumfordBundle f L 𝓛)) := by sorry
