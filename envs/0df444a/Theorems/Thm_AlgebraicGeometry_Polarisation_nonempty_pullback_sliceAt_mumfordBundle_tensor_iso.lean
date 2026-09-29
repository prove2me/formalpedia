-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_tensor_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2e16b0c5-6b5e-5abf-87df-171687c05ff3
-- title:
--   Slices of the Mumford bundle are multiplicative
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: for every $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set of morphisms $T \to A$ over $\operatorname{Spec} k$, satisfying associativity, the unit laws and left inverses, and compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Let $\mathcal L, \mathcal L'$ be modules on $A$, each invertible in the sense that every point of $A$ has an open neighbourhood $U$ such that the restriction along $U \hookrightarrow A$ is isomorphic to the unit module of $U$. For such a module $\mathcal M$ the Mumford bundle on $A \times_k A$ is $\mu^*\mathcal M \otimes (p_1^*\mathcal M^\vee \otimes p_2^*\mathcal M^\vee)$, where $p_1, p_2$ are the two projections, $\mu$ is the morphism obtained by multiplying them with the group law, and $\mathcal M^\vee$ is the internal hom from $\mathcal M$ to the unit. Finally let $t : T \to \operatorname{Spec} k$ be a $k$-scheme and $x$ a morphism $T \to A$ with $x$ followed by $f$ equal to $t$. The assertion is that the set of isomorphisms, on $A \times_k T$, between the pullback of the Mumford bundle of $\mathcal L \otimes \mathcal L'$ along the morphism $A\times_k T \to A \times_k A$ with components $p_1$ and $p_2$ followed by $x$, and the tensor product of the pullbacks along that same morphism of the Mumford bundles of $\mathcal L$ and of $\mathcal L'$, is nonempty.
--
--   This is the multiplicativity in the line bundle of the slices of the Mumford bundle, the bundle-level form of the additivity $\varphi_{\mathcal L\otimes\mathcal L'}=\varphi_{\mathcal L}+\varphi_{\mathcal L'}$ of the maps to the dual abelian variety. It is used in the study of the stabiliser (the scheme-theoretic kernel $K(\mathcal L)$) and of tensor powers of polarising bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_sliceAt_mumfordBundle_tensor_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_sliceAt_mumfordBundle_tensor_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of k)} (x : SchemeHomOver t f) :
    Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L (𝓛 ⊗ 𝓛')) ≅ (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛) ⊗ (Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛')) := by sorry
