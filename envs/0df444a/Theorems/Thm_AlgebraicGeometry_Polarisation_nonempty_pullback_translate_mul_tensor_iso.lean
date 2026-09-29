-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translate_mul_tensor_iso
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_translate_mul_tensor_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/ee839e49-436d-57b3-b15a-c727905b86b6
-- title:
--   Theorem of the square for a commutative relative group law
-- statement:
--   Let $k$ be an algebraically closed field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes (in universe $0$). Suppose given a relative group law $L$ on $f$, that is, functorial multiplication, unit and inversion operations on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} k$, satisfying associativity, the unit laws, left inversion and compatibility with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$; assume $L$ is commutative, i.e. $L.\mathrm{mul}\,t\,x\,y = L.\mathrm{mul}\,t\,y\,x$ for all $T$-points. Assume further the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathcal L$ be a sheaf of modules on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $\mathcal L$ is isomorphic to the unit module, and let $x, y$ be points of $A$ over the identity of $\operatorname{Spec} k$, i.e. sections $\operatorname{Spec} k \to A$ of $f$. Writing $T_z$ for $L.\mathrm{translate}\,z$, the endomorphism of $A$ obtained by multiplying the identity point of $A$ with the constant point $f$ followed by $z$, the assertion is that there exists an isomorphism $$T_{x\cdot y}^{*}\mathcal L \otimes \mathcal L \;\cong\; T_x^{*}\mathcal L \otimes T_y^{*}\mathcal L$$ of modules on $A$, where $x \cdot y = L.\mathrm{mul}\,(\mathbf 1_{\operatorname{Spec} k})\,x\,y$ and $\otimes$ is the monoidal product of sheaves of modules.
--
--   This is the theorem of the square for an abelian variety over an algebraically closed field, equivalently the statement that $x \mapsto T_x^{*}\mathcal L \otimes \mathcal L^{-1}$ is a homomorphism from the group of $k$-points of $A$ to $\operatorname{Pic}(A)$. It is stated here for the project's relative-group-law presentation of the group structure, and is used in the treatment of $\operatorname{Pic}^0$ and of polarisations, for instance in the results on membership of pullbacks along translations and along inversion in $\operatorname{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translate_mul_tensor_iso.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_translate_mul_tensor_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty (
      (Scheme.Modules.pullback (L.translate (L.mul (𝟙 (Spec (CommRingCat.of k))) x y))).obj 𝓛 ⊗ 𝓛 ≅
      (Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗ (Scheme.Modules.pullback (L.translate y)).obj 𝓛) := by sorry
