-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_inPicZero_iff_forall_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
-- name    : AlgebraicGeometry.Polarisation.inPicZero_iff_forall_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/c1594dc2-84ba-58ca-9dfa-f9c4ddd2d66d
-- title:
--   M ∈ Pic⁰ iff all point slices of Λ(M) are trivial
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme, $f : A \to \operatorname{Spec} k$ a morphism, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ ... \}$ of $T$-points of $f$ over each $t : T \to \operatorname{Spec} k$ (the Lean `SchemeHomOver t f`, pairs of a morphism $\varphi$ with $\varphi$ followed by $f$ equal to $t$), with multiplication, unit, inverse, the group axioms and naturality in $T$. Let $M$ be a module over $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ with the restriction of $M$ along $U \hookrightarrow A$ isomorphic to the unit sheaf of modules on $U$. The assertion is the equivalence of: (i) `InPicZero f L M`, namely that $M$ is invertible and for every $k$-point $x$ of $f$ (a section of $f$ over the identity of $\operatorname{Spec} k$) the pullback of $M$ along the translation $T_x = L.\mathrm{translate}\,x$ is isomorphic to $M$; and (ii) for every such $x$, the pullback of the Mumford bundle $\Lambda(M) = m^*M \otimes (p_1^*M^\vee \otimes p_2^*M^\vee)$ on $A \times_k A$ — where $m$ is the morphism `addMor f L` multiplying the two projections, $p_1, p_2$ are the projections, and $M^\vee$ is the internal hom from $M$ to the unit — along the slice $\mathrm{sliceAt}\,f\,x = (p_1, p_2 \circ x) : A \times_{\operatorname{Spec} k} \operatorname{Spec} k \to A \times_k A$ is isomorphic to the unit module. Side (ii) does not itself assert invertibility; the hypothesis that $M$ is invertible is what supplies that half of (i).
--
--   This is the standard criterion identifying $\mathrm{Pic}^0$ of an abelian variety, in the form "$T_x^*M \cong M$ for all rational points $x$ if and only if all point slices $(\mathrm{id} \times x)^*\Lambda(M)$ of the Mumford bundle are trivial", here for a scheme over an algebraically closed field equipped with a relative group law. It is the bridge between the translation-invariance description of $\mathrm{Pic}^0$ and the $\Lambda$-bundle vocabulary, and is used for the variant in which a single isomorphism $\Lambda(M) \cong \mathcal{O}$ on $A \times A$ is assumed, and for recovering $T_x^*M \otimes M^\vee \cong \mathcal{O}$ from such an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_inPicZero_iff_forall_nonempty_pullback_sliceAt_mumfordBundle_iso_unit.lean

import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.inPicZero_iff_forall_nonempty_pullback_sliceAt_mumfordBundle_iso_unit
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) :
    InPicZero f L M ↔
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, Nonempty ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L M) ≅ 𝟙_ ((pullback f (𝟙 (Spec (CommRingCat.of k)))).Modules)) := by sorry
