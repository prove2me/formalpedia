-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_negMor_tensor_dual
-- name    : AlgebraicGeometry.Polarisation.inPicZero_pullback_negMor_tensor_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/25d7863b-1733-5c90-b005-fd10f312892f
-- title:
--   [-1]^*LotimesL^∨ lies in Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a structure morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$ in the sense of the structure `RelativeGroupLaw`: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$, compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Assume this group law is commutative, and assume `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ carries a relative group law. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module on $U$. Write $[-1] =$ `negMor f L` for the underlying morphism $A \to A$ of the inverse, under $L$, of the identity section $\mathrm{id}_A$ over $f$, and $\mathcal L^\vee$ for the internal hom from $\mathcal L$ into the unit. Then $[-1]^*\mathcal L \otimes \mathcal L^\vee$ satisfies `InPicZero f L`: it is invertible, and for every section $x$ of $f$ over $\operatorname{Spec} k$ its pullback along the translation morphism $L.\mathrm{translate}\,x$ is isomorphic to itself.
--
--   This is the statement that $\varphi_{[-1]^*\mathcal L} = \varphi_{\mathcal L}$ for a line bundle on an abelian variety, in the form '$[-1]^*\mathcal L\otimes\mathcal L^\vee$ is translation-invariant'. It is used in the construction of symmetric elements of the relative Picard group (symmetrisation of a line bundle underlying a polarisation) and in the comparison of Rosati-compatibility and of fibrewise $H^0$-dimensions for $\mathcal L$ and for $[-1]^*\mathcal L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_inPicZero_pullback_negMor_tensor_dual.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.Polarisation.inPicZero_pullback_negMor_tensor_dual
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    InPicZero f L ((Scheme.Modules.pullback (negMor f L)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by sorry
