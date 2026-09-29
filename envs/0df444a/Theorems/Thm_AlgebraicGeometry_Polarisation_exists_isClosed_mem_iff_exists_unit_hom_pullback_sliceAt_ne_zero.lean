-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
-- name    : AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/3bb4d2dd-8223-5824-ac6b-3cc591a338a5
-- title:
--   Closed locus of k-points whose slice of Λ has sections
-- statement:
--   Let $k$ be an algebraically closed field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes. Assume given: a relative group law `L` for $f$, i.e. functorial multiplication, unit and inverse operations on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $k$, satisfying associativity, the two unit laws and left inversion, and compatible with base change along maps $T' \to T$ over $k$; a bundle `hA` asserting that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ is connected, and that a relative group law for $f$ exists; and a module $\Lambda$ on the scheme $A \times_k A$ which is invertible in the sense that every point of $A \times_k A$ has an open neighbourhood $U$ on which the restriction of $\Lambda$ is isomorphic to the unit module of $U$. The conclusion is that there is a closed subset $Z$ of the underlying space of $A$ such that, for every $k$-point $x$ of $A$ (a morphism $\operatorname{Spec} k \to A$ composing with $f$ to the identity), the image of the closed point of $\operatorname{Spec} k$ under $x$ lies in $Z$ if and only if there is a nonzero morphism from the unit module on $A \times_k \operatorname{Spec} k$ (formed with the identity of $\operatorname{Spec} k$) to the pullback of $\Lambda$ along `sliceAt f x`, the map $A \times_k \operatorname{Spec} k \to A \times_k A$ with components the first projection and the second projection followed by $x$. Thus $Z$ cuts out, on $k$-points, the locus where the slice $\Lambda|_{A \times \{x\}}$ admits a nonzero global section.
--
--   This is the semicontinuity statement behind the standard fact that, for an invertible module on $A \times_k A$, the set of $k$-points $x$ with $H^0(A \times \{x\}, \Lambda|_{A \times \{x\}}) \neq 0$ is closed; it is the topological input for the study of polarisations and the Rosati involution on abelian schemes. It is used to obtain the corresponding closed locus where the slice is isomorphic to the unit module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero.lean

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

theorem AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_exists_unit_hom_pullback_sliceAt_ne_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (Λ : (pullback f f).Modules) (hΛ : Scheme.Modules.IsInvertible Λ) :
    ∃ Z : Set A, IsClosed Z ∧ ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
      x.1.base (IsLocalRing.closedPoint k) ∈ Z ↔
        ∃ s : 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules ⟶ (Scheme.Modules.pullback (sliceAt f x)).obj Λ, s ≠ 0 := by sorry
