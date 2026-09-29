-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
-- name    : AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/b8053a3b-151a-5cb0-ac8f-f24e383637f4
-- title:
--   Stabiliser points and triviality of the sliced Mumford bundle
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a relative group law on $f$ over $k$: a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inverse, and naturality in $T$. Let $\mathcal L$ be a module on $A$ which is invertible, i.e. every point of $A$ has an open neighbourhood $U$ such that the restriction of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit module. Let $R$ be a commutative ring, $t : \operatorname{Spec} R \to \operatorname{Spec} k$, and $x$ a morphism $\operatorname{Spec} R \to A$ with $x$ followed by $f$ equal to $t$. The assertion is the equivalence of two conditions, each of the form 'locally on the base $\operatorname{Spec} R$': writing $q = p_2 : A \times_{\operatorname{Spec} k} \operatorname{Spec} R \to \operatorname{Spec} R$, a pair of modules $M, M'$ on $A\times_k\operatorname{Spec} R$ is so related when every point $s \in \operatorname{Spec} R$ has an open neighbourhood $U$ with the restrictions of $M$ and $M'$ to $q^{-1}U$ isomorphic. The first condition, `L.IsInStabilizer 𝓛 t x`, compares $m_x^*\mathcal L$ with $p_1^*\mathcal L$, where $m_x =$ `L.mulRight t x` is the morphism to $A$ obtained by multiplying, in the group law, the point $p_1$ by the point $p_2$ followed by $x$. The second compares the pullback along `sliceAt f x` $= (p_1, p_2 \circ x) : A\times_k \operatorname{Spec} R \to A\times_k A$ of the Mumford bundle $\mu^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$, where $\mu$ is the multiplication morphism of $L$ and $\mathcal L^\vee$ is the internal hom from $\mathcal L$ to the unit, with the unit module.
--
--   This is the dictionary between two descriptions of the points of the stabiliser $K(\mathcal L)$ of an invertible sheaf under translation: membership in the stabiliser on $R$-points, and triviality, locally on $\operatorname{Spec} R$, of the slice at $x$ of the Mumford bundle $\Lambda(\mathcal L)$. It is used by the statements about $K(\mathcal L)$ phrased in terms of the Mumford bundle, such as those on Čech cohomology of the sliced bundle and on the kernel of a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f) :
    L.IsInStabilizer 𝓛 t x ↔
      LocIsoOnBase (pullback.snd f t) ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f t).Modules)) := by sorry
