-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/52355662-97a3-5a5b-a95c-a34bf05ed8e3
-- title:
--   Two-chart Čech H¹ vanishes if all field fibres vanish
-- statement:
--   Let $A$ be a commutative ring, let $X$ be a scheme and let $\pi \colon X \to \operatorname{Spec} A$ be a morphism. Let $\mathcal V$ be a `TwoAffineOpenCover` of $X$, that is, a pair of opens $U_0, U_1$, each affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, and let $F$ be a sheaf of modules on $X$. Here $(\mathcal V.\mathrm{sectionsOf}\ \pi\ F).H_1$ denotes the cokernel of the $A$-linear map $\Gamma(F, U_0) \oplus \Gamma(F, U_1) \to \Gamma(F, U_0 \sqcap U_1)$, $(s_0, s_1) \mapsto s_1|_{U_0 \sqcap U_1} - s_0|_{U_0 \sqcap U_1}$, the $A$-module structures coming from $\pi$. Assume: (i) every point $x$ of $X$ lies in some open $V$ such that the pullback of $F$ along the inclusion $V \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $V$; (ii) this $H^1$ is a finite $A$-module; (iii) for every field $K$ (in the same universe) equipped with an $A$-algebra structure, the corresponding $H^1$ for the base-changed cover $\mathcal V.\mathrm{pullback}\ \pi\ K$ on $X \times_{\operatorname{Spec} A} \operatorname{Spec} K$, taken with respect to the second projection and the pullback of $F$ along the first projection, is a subsingleton. Then $(\mathcal V.\mathrm{sectionsOf}\ \pi\ F).H_1$ is a subsingleton.
--
--   This is the top-degree case of cohomology and base change, in the two-chart Čech form: since the Čech complex has length one, its cokernel commutes with arbitrary base change without flatness hypotheses, so vanishing on all field-valued fibres forces vanishing over the base. It is used in the construction of the relative Picard functor, namely in [`AlgebraicGeometry.RelPicard.exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
    {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1) :
    Subsingleton (𝒱.sectionsOf π F).H1 := by sorry
