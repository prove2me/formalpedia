-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullbackAlong_openCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/fcd78912-4405-56df-ab94-497b4939240f
-- title:
--   Fibrewise algebraic triviality descends along open covers of the base
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a scheme over $\operatorname{Spec} R$ and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $t : T \to \operatorname{Spec} R$ be a further $R$-scheme, let $\iota$ index schemes $U i$ with structure morphisms $u i : U i \to \operatorname{Spec} R$, and for each $i$ let $f i$ be a morphism $U i \to T$ with $f i$ followed by $t$ equal to $u i$, whose underlying scheme morphism is an open immersion; assume every point of $T$ lies in the image of the base map of some $f i$. Let $M$ be a rigidified line bundle on $c$ over $t$: an invertible module $M.L$ on $C \times_{\operatorname{Spec} R} T$ (locally isomorphic to the unit module) together with a trivialisation of its pullback along the rigidifying section $T \to C \times_{\operatorname{Spec} R} T$ determined by $\varepsilon$. Suppose that for each $i$ the pullback of $M$ along $f i$, namely $M.L$ pulled back by the base change $C \times_{\operatorname{Spec} R} U i \to C \times_{\operatorname{Spec} R} T$, satisfies `FibrewiseAlgEquivZero`. Then $M$ satisfies `FibrewiseAlgEquivZero`: for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to T$, the pullback of $M.L$ to the fibre $(C \times_{\operatorname{Spec} R} T) \times_T \operatorname{Spec} k$ is algebraically equivalent to zero over $\operatorname{Spec} k$, in the sense that there are a scheme $T'$ over $k$ whose structure morphism is locally of finite type and geometrically integral, an invertible module on the product of the fibre with $T'$, and two $k$-sections of $T'$ along which that module restricts to the unit module and to the pullback of the given one respectively.
--
--   This is the statement that the condition "algebraically equivalent to zero on all geometric fibres" is Zariski-local on the test scheme $T$: it holds for a rigidified line bundle as soon as it holds for its restrictions to the members of an open cover of $T$. It is the locality ingredient used in establishing the Zariski sheaf property of the subpresheaf of the relative Picard functor cut out by fibrewise algebraic equivalence to zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.fibrewiseAlgEquivZero_of_pullbackAlong_openCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M : RigidifiedLineBundle c ε t) (h : ∀ i, FibrewiseAlgEquivZero (M.pullbackAlong (f i))) :
    FibrewiseAlgEquivZero M := by sorry
