-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/e01d0a96-da34-57a9-9751-231396ffe07f
-- title:
--   Left slice of the Mumford bundle at a k-point
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ for $f$: that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections of $f$ over each $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse natural in $T$. Assume $L$ is commutative, i.e. its multiplication on sections over every base is commutative. Let $\mathcal{L}$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit module, and let $y$ be a section of $f$ over the identity of $\operatorname{Spec} k$, i.e. a morphism $y : \operatorname{Spec} k \to A$ with $y$ followed by $f$ the identity. Write $\sigma : A \to A \times_{\operatorname{Spec} k} A$ for the morphism with first component $f$ followed by $y$ and second component $\mathrm{id}_A$, the inclusion of the slice $\{y\} \times A$, and let $\Lambda(\mathcal{L}) = m^*\mathcal{L} \otimes (p_1^*\mathcal{L}^\vee \otimes p_2^*\mathcal{L}^\vee)$ be the Mumford bundle on $A \times_{\operatorname{Spec} k} A$, where $m$ is the multiplication morphism supplied by $L$ on the fibre product, $p_1, p_2$ are the projections and $\mathcal{L}^\vee$ is the internal hom from $\mathcal{L}$ into the unit. The assertion is that there exists an isomorphism $\sigma^*\Lambda(\mathcal{L}) \cong T_y^*\mathcal{L} \otimes \mathcal{L}^\vee$ of modules on $A$, where $T_y : A \to A$ is the translation given by multiplying the identity section by the constant section $f$ followed by $y$. The conclusion records only the nonemptiness of the set of such isomorphisms, not a chosen one.
--
--   This is the left-slice computation for the Mumford (theorem-of-the-square) bundle $\Lambda(\mathcal{L})$ on $A \times A$: restricted to $\{y\} \times A$ it becomes $T_y^*\mathcal{L} \otimes \mathcal{L}^\vee$. It is the companion of the right-slice computation and feeds the see-saw argument used in identifying elements of $\mathrm{Pic}^0$ with translation-invariant bundles; here it is cited in the analysis of bundles with finite kernel of translation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_leftSlice_mumfordBundle_iso_pullback_translate_tensor_dual
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.lift (f ≫ y.1) (𝟙 A) (by rw [Category.assoc, y.2, Category.comp_id, Category.id_comp]))).obj (mumfordBundle f L 𝓛) ≅
      (Scheme.Modules.pullback (L.translate y)).obj 𝓛 ⊗ Scheme.Modules.dual 𝓛) := by sorry
