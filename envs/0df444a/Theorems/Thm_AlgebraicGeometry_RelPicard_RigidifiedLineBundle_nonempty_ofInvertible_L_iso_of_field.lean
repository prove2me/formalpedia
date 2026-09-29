-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/eba19735-2520-52cc-8c65-c9656c1c0507
-- title:
--   Over a field-valued point the rigidification recovers L
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity of $\operatorname{Spec} R$. Let $K$ be a field and $t : \operatorname{Spec} K \to \operatorname{Spec} R$ any morphism, and let $L$ be a sheaf of modules on the fibre product $\operatorname{pullback} c\, t = C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ which is invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: every point of the fibre product has an open neighbourhood $U$ such that the restriction of $L$ to $U$ is isomorphic to the unit sheaf of modules on $U$. Then the underlying module of the rigidified line bundle `RigidifiedLineBundle.ofInvertible` attached to $L$, namely $L \otimes q^{*}\bigl((\sigma^{*}L)^{\vee}\bigr)$ where $q = \operatorname{pullback.snd} c\, t$ is the projection to $\operatorname{Spec} K$, $\sigma = \operatorname{rigSection} c\, t\, \varepsilon$ is the section of $q$ determined by $t$ followed by $\varepsilon$, and $(-)^{\vee}$ is the internal dual in the monoidal category of modules, is isomorphic to $L$ itself; the conclusion is the non-emptiness of the type of such isomorphisms.
--
--   This is the statement that over a base point with values in a field the canonical rigidification procedure changes nothing: since the Picard group of the spectrum of a field is trivial, every invertible module on $C \times_R \operatorname{Spec} K$ is already rigidified along the given section. It is used when identifying classifying morphisms into the relative Picard functor after base change to a residue field or to a field-valued point, and is cited in the construction of points of Néron models attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {L : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅ L) := by sorry
