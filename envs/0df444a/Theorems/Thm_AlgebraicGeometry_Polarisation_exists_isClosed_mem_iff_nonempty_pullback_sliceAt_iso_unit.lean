-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit
-- name    : AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/b7884949-e977-58ab-bb18-6756a436bd7c
-- title:
--   Closedness of the locus of trivial slices of an invertible module
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism. Assume given a relative group law $L$ for $f$, that is, functorial multiplication, unit and inversion operations on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of points of $A$ over an arbitrary $k$-scheme $t : T \to \operatorname{Spec} k$, satisfying associativity, the two unit laws, left inversion, and compatibility with base change along $\psi : T' \to T$; and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, $f$ is proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\Lambda$ be a module on the fibre product $A \times_{\operatorname{Spec} k} A$ which is invertible in the sense that every point of that scheme has an open neighbourhood $U$ whose restriction $\Lambda|_U$ is isomorphic to the unit sheaf of modules on $U$. The conclusion asserts the existence of a closed subset $Z \subseteq A$ with the following property: for every section $x$ of $f$ over the identity of $\operatorname{Spec} k$, i.e. every $\varphi : \operatorname{Spec} k \to A$ with $\varphi \circ f = \mathrm{id}$, the image of the closed point of $k$ under $\varphi$ lies in $Z$ if and only if the pullback of $\Lambda$ along `sliceAt f x`, the morphism $A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times_{\operatorname{Spec} k} A$ with components the first projection and the second projection followed by $\varphi$, is isomorphic to the monoidal unit among the modules on $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$.
--
--   This is the closedness of the locus of points $x$ of an abelian variety at which the slice $\Lambda|_{A \times \{x\}}$ of an invertible module on $A \times A$ is trivial, a step in the see-saw style analysis used to set up polarisations and the Rosati involution. It is cited in the construction of the corresponding closed locus for translations in the Riemann-form part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ) :
    ∃ Z : Set A, IsClosed Z ∧ ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1.base (IsLocalRing.closedPoint k) ∈ Z ↔
        Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj Λ ≅ 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules) := by sorry
