-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d3132dfe-146e-5ecc-8ef0-124fb5aa909b
-- title:
--   Descent of rigidified line bundles along affine faithfully flat base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism, equipped with $\varepsilon$, a morphism $\operatorname{Spec} R \to C$ satisfying $\varepsilon \mathbin{;} c = \mathrm{id}$. Assume the cohomological hypothesis `hH0`: for every $R$-algebra $A$, the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \mathcal{O})$ coming from the second projection is bijective. Let $t \colon T \to \operatorname{Spec} R$ and $t' \colon T' \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$ and let $\pi \colon T' \to T$ satisfy $\pi \mathbin{;} t = t'$, with $\pi$ affine, flat and surjective. Let $M'$ be an $\varepsilon$-rigidified line bundle on $T'$ in the sense of `RigidifiedLineBundle`: a module $M'.L$ on $C \times_{\operatorname{Spec} R} T'$ which is invertible (every point has an open neighbourhood over which the restriction is isomorphic to the unit sheaf of modules) together with an isomorphism of its pullback along the rigidifying section $\operatorname{rigSection}$, the map $T' \to C \times_{\operatorname{Spec} R} T'$ with components $t' \mathbin{;} \varepsilon$ and $\mathrm{id}_{T'}$, with the unit sheaf of modules on $T'$. Assume further that for every scheme $Z$ over $\operatorname{Spec} R$ and every pair of $\operatorname{Spec} R$-morphisms $p_1, p_2 \colon Z \to T'$ with $p_1 \mathbin{;} \pi = p_2 \mathbin{;} \pi$, the underlying modules of the pullbacks of $M'$ along $p_1$ and along $p_2$ (pullback along the base change $\mathrm{id}_C \times p_i$) are isomorphic. Then there exists an $\varepsilon$-rigidified line bundle $M$ on $T$ whose pullback along $\mathrm{id}_C \times \pi$ has underlying module isomorphic to $M'.L$. The conclusion asserts only an isomorphism of the underlying modules, not one compatible with the rigidifications.
--
--   This is effective faithfully flat descent for rigidified line bundles on a curve-like family $C \to \operatorname{Spec} R$, in the form used for the rigidified relative Picard functor (Bosch–Lütkebohmert–Raynaud, Néron Models 8.1); the hypothesis that $A \to \Gamma(C \times_R \operatorname{Spec} A, \mathcal{O})$ is always bijective is what makes rigidified line bundles have no nontrivial automorphisms, so that the descent datum is determined by the isomorphisms assumed in `hM'`. It feeds the study of the Jacobian of a smooth proper curve, being cited in the proof that the class functor of the associated abelian-scheme property bundle is injective with the required existence property.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_descent_of_isAffineHom_of_flat_of_surjective_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (π : SchemeHomOver t' t) [IsAffineHom π.1] [Flat π.1] [Surjective π.1]
    (M' : RigidifiedLineBundle c ε t')
    (hM' : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
      (p₁ p₂ : SchemeHomOver z t'),
      p₁.1 ≫ π.1 = p₂.1 ≫ π.1 →
        Nonempty ((M'.pullbackAlong p₁).L ≅ (M'.pullbackAlong p₂).L)) :
    ∃ M : RigidifiedLineBundle c ε t, Nonempty ((M.pullbackAlong π).L ≅ M'.L) := by sorry
