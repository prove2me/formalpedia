-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
-- name    : AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/dea44e27-c784-52d3-b528-39542720f186
-- title:
--   Descent of rigidified line bundles along finite faithfully flat base change: uniqueness
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ$-composite $c$ equal to the identity. Assume the universal sections hypothesis `hH0`: for every $R$-algebra $A$, the structure map $A \to \Gamma(C \times_{\operatorname{Spec} R} \operatorname{Spec} A, \top)$ coming from the second projection is bijective. Let $R'$ be an $R$-algebra which is finite and faithfully flat as an $R$-module, and let $t \colon T \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$. Let $M_1, M_2$ be rigidified line bundles for $(c, \varepsilon)$ over $t$: each consists of a module $L$ on $C \times_{\operatorname{Spec} R} T$ which is invertible (locally on the source isomorphic to the unit sheaf of rings of functions), together with an isomorphism of its pullback along the section $T \to C \times_{\operatorname{Spec} R} T$ determined by $t$ followed by $\varepsilon$ and the identity of $T$ with the unit sheaf on $T$. Write $T' = T \times_{\operatorname{Spec} R} \operatorname{Spec} R'$, viewed over $T$ by the first projection. If the underlying modules of the base changes of $M_1$ and $M_2$ to $C \times_{\operatorname{Spec} R} T'$ are isomorphic, then the underlying modules $M_1.L$ and $M_2.L$ on $C \times_{\operatorname{Spec} R} T$ are isomorphic. Only the underlying modules are compared; the isomorphisms are not required to respect the rigidifications.
--
--   This is the uniqueness (injectivity) half of the sheaf property of the rigidified relative Picard functor for the finite faithfully flat covering $\operatorname{Spec} R' \to \operatorname{Spec} R$, in the form used for Néron models of curves. It feeds the proof that the relative sub-Picard presheaf satisfies the sheaf condition for such coverings, and is also used in comparing invertible modules with the unit module after pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections.lean

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

theorem AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_finite_faithfullyFlat_of_bijective_sections
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M₁ M₂ : RigidifiedLineBundle c ε t)
    (h : Nonempty ((M₁.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L ≅
      (M₂.pullbackAlong ⟨pullback.fst t (specMap R R'), pullback.condition⟩).L)) :
    Nonempty (M₁.L ≅ M₂.L) := by sorry
