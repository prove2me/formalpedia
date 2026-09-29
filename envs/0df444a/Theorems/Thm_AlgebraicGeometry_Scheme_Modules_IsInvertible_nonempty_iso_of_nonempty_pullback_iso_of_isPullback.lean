-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/5abd03de-4ac1-5e12-87ed-5d4fe5c0c22b
-- title:
--   Invertible modules on an abelian variety descend along a field extension
-- statement:
--   Let $k$ be a field and $f : A \to \operatorname{Spec} k$ a morphism of schemes satisfying the predicate `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, the fibre $f^{-1}(s)$ over every point $s$ of $\operatorname{Spec} k$ is connected, and $f$ admits a relative group law (a functorial group structure on the sets of $T$-points over $\operatorname{Spec} k$, compatible with base change in $T$). Let $\mathcal L, \mathcal L'$ be modules over $A$ that are invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ such that the pullback of the module along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module on $U$. Let $k'$ be a field, $\varphi : k \to k'$ a ring homomorphism, and let $f' : A' \to \operatorname{Spec} k'$ and $g : A' \to A$ form a cartesian square with $f$ and $\operatorname{Spec} \varphi$, so that $A'$ is a fibre product $A \times_{\operatorname{Spec} k} \operatorname{Spec} k'$. If the pullbacks $g^*\mathcal L$ and $g^*\mathcal L'$ are isomorphic, then $\mathcal L$ and $\mathcal L'$ are isomorphic. Both isomorphism hypothesis and conclusion are stated as `Nonempty` of the type of isomorphisms, i.e. as mere existence of an isomorphism.
--
--   This is the descent of isomorphism classes of line bundles on an abelian variety along an arbitrary extension of the base field, stated for an arbitrary cartesian square rather than for the chosen fibre product. It is used when comparing polarisations after base change, in particular by the compatibility of the Rosati involution with base change and in the analysis of canonical polarisations on fake elliptic curves over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_nonempty_pullback_iso_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 𝓛' : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (k' : Type) [Field k'] (φ : k →+* k') {A' : Scheme} (f' : A' ⟶ Spec (CommRingCat.of k')) (g : A' ⟶ A)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    (h : Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ (Scheme.Modules.pullback g).obj 𝓛')) :
    Nonempty (𝓛 ≅ 𝓛') := by sorry
