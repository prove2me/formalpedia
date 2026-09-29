-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f31dbc49-bd33-5ef4-8087-5a89b370439c
-- title:
--   [n]^*L ≅ L^{⊗ n^2} for symmetric invertible sheaves
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism. Let $L$ be a relative group law for $f$, that is, a family of group structures on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} k$ (multiplication, unit and inverse, with associativity, the two unit laws, left inverses, and naturality of multiplication under precomposition with morphisms $\psi : T' \to T$ over $\operatorname{Spec} k$), and assume `hc`, that each of these group structures is commutative. Assume `hA`, the bundle `AbelianSchemePropertyBundle k f`: $f$ is smooth and proper, the fibre $f^{-1}(s)$ is connected for every point $s$ of $\operatorname{Spec} k$, and a relative group law for $f$ exists. Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module of $U$, and assume `hsym`: $\mathcal L$ is symmetric, i.e. the pullback of $\mathcal L$ along the inversion morphism `negMor f L` (the underlying morphism of the inverse of the identity point) and $\mathcal L$ become isomorphic after restriction to $f^{-1}(U)$ for some open $U$ around each point of $\operatorname{Spec} k$. Then, for every natural number $n$, the pullback of $\mathcal L$ along `L.schemeNsmul n` — the underlying morphism of the $n$-fold group-law sum of the identity point of $A$ with itself, i.e. multiplication by $n$ — admits an isomorphism to $\mathcal L^{\otimes n^2}$, where tensor powers are defined by $\mathcal L^{\otimes 0} = \mathcal O_A$ and $\mathcal L^{\otimes(m+1)} = \mathcal L^{\otimes m} \otimes \mathcal L$. The conclusion asserts nonemptiness of the type of such isomorphisms rather than exhibiting a chosen one.
--
--   This is the symmetric case of Mumford's computation of $[n]^*\mathcal L$ on an abelian variety, a consequence of the theorem of the cube, here in the form of a statement about a scheme over an algebraically closed field carrying a commutative relative group law. It feeds the analysis of the groups $\mathcal L^{\otimes m}$ and their kernel points used in the subsingleton statement for the associated Picard data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_schemeNsmul_iso_tensorPow_sq_of_isSymmetric_monoidalV2
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hsym : IsSymmetric f L 𝓛) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓛 ≅ 𝓛.tensorPow (n ^ 2)) := by sorry
