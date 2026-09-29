-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_ne_zero_section_dual_slice
-- name    : AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_ne_zero_section_dual_slice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/654223a5-b1f1-5c52-97aa-b4bad071ca66
-- title:
--   Invertible module with non-zero section and co-section on a slice
-- statement:
--   Let $k$ be a field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes (in universe $0$, with $\operatorname{Spec} k$ formed from the commutative ring $k$). Assume given a `RelativeGroupLaw` $L$ for $f$, i.e. a functorial group structure on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for all $t : T \to \operatorname{Spec} k$ (multiplication, unit and inverse, associativity, the two unit laws, left inverse law, and compatibility with base change $\psi : T' \to T$ over $\operatorname{Spec} k$), and assume `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $P = A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ be the pullback of $f$ along the identity of $\operatorname{Spec} k$, and let $M$ be a module on $P$ that is invertible in the sense that every point of $P$ has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit sheaf of modules on $U$. Suppose given morphisms $s : \mathcal{O} \to M$ and $s' : \mathcal{O} \to M^{\vee}$ from the monoidal unit, where $M^{\vee}$ is the internal hom from $M$ to the unit, and suppose $s \neq 0$ and $s' \neq 0$. Then the type of isomorphisms $M \cong \mathcal{O}$ on $P$ is nonempty.
--
--   This is the standard fact that on an abelian variety an invertible sheaf possessing a non-zero section and a non-zero section of its dual is trivial, transported from $A$ itself to the slice $A \times_{\operatorname{Spec} k} \operatorname{Spec} k$ obtained as a pullback along the identity. It is used in the assembly of the closedness of the locus of points of the base over which a line bundle becomes trivial, via [`AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit`](thm.html#AlgebraicGeometry.Polarisation.exists_isClosed_mem_iff_nonempty_pullback_sliceAt_iso_unit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_iso_unit_of_ne_zero_section_dual_slice.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_iso_unit_of_ne_zero_section_dual_slice
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (M : (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ _ ⟶ M) (s' : 𝟙_ _ ⟶ Scheme.Modules.dual M) (hs : s ≠ 0) (hs' : s' ≠ 0) :
    Nonempty (M ≅ 𝟙_ (pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules) := by sorry
