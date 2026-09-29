-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero
-- name    : AlgebraicGeometry.Polarisation.nonempty_phi_tensor_iso_phi_of_inPicZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/3de684e1-d9cc-52c4-8df6-cc5f4aeab74a
-- title:
--   Translation quotient unchanged by twisting by Pic⁰
-- statement:
--   Let $k$ be a field, assumed algebraically closed, let $A$ be a scheme, let $f : A \to \operatorname{Spec} k$ be a morphism, and let $L$ be a `RelativeGroupLaw` for $f$, i.e. a functorial group law on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ\text{-over-}t\}$ of $T$-points of $A$ over $\operatorname{Spec} k$ (operations `mul`, `one`, `inv`, with associativity, both unit laws, left inverses, and naturality under base change $\psi : T' \to T$). Let $\mathcal L$ and $M$ be sheaves of modules on $A$. Assume $\mathcal L$ is invertible in the project's sense: every point of $A$ has an open neighbourhood $U$ such that the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of $U$. Assume `InPicZero f L M`, i.e. $M$ is invertible in the same sense and, for every $k$-point $y$ of $A$, the pullback of $M$ along the translation $T_y = L.\mathrm{translate}\,y$ (the morphism $A \to A$ obtained by multiplying the identity point of $A$ by the constant point $y$) is isomorphic to $M$. Finally let $x$ be a $k$-point of $A$. The conclusion is that the type of isomorphisms $T_x^{*}(\mathcal L \otimes M) \otimes (\mathcal L \otimes M)^{\vee} \cong T_x^{*}\mathcal L \otimes \mathcal L^{\vee}$ of modules on $A$ is nonempty, where the dual is the internal hom into the unit object.
--
--   This is the standard fact that the morphism $\varphi_{\mathcal L} : x \mapsto T_x^{*}\mathcal L \otimes \mathcal L^{\vee}$ attached to an invertible sheaf depends only on the class of $\mathcal L$ modulo $\mathrm{Pic}^0$, in the pointwise form needed before $\varphi_{\mathcal L}$ is assembled into a morphism of group schemes. It is used to identify the kernel points of $\varphi_{\mathcal L \otimes M}$ with those of $\varphi_{\mathcal L}$, in the construction of polarisations of abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_phi_tensor_iso_phi_of_inPicZero.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_phi_tensor_iso_phi_of_inPicZero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓛 M : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hM : InPicZero f L M) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty (
      (Scheme.Modules.pullback (L.translate x)).obj (𝓛 ⊗ M) ⊗ Scheme.Modules.dual (𝓛 ⊗ M) ≅
      (Scheme.Modules.pullback (L.translate x)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by sorry
