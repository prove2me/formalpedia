-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/40431f77-c5f9-5b37-af1e-48577cb8a63b
-- title:
--   Base field extension preserves two-chart Čech h⁰ and H¹-vanishing
-- statement:
--   Let $k$ be a field, $X$ a scheme with a morphism $x : X \to \operatorname{Spec} k$, and $\mathcal V$ a `TwoAffineOpenCover` of $X$, i.e. a pair of opens $U_0, U_1$, each affine, with affine intersection and $U_0 \sqcup U_1 = \top$. Let $M$ be a module over $X$ which is locally trivial in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of the structure sheaf of $U$. Let $k'$ be a field with a $k$-algebra structure. Form the fibre product of $x$ with $\operatorname{Spec}$ of the structure map $k \to k'$; its cover by the preimages of $U_0, U_1$ under the first projection, its structure morphism to $\operatorname{Spec} k'$ given by the second projection, and the pullback of $M$ along the first projection. Attached to such data is the two-term complex $(-r_0) \sqcup r_1 : \Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M, U_0 \sqcap U_1)$ built from the two restriction maps, with $H^0$ its kernel and $H^1$ the quotient of $\Gamma(M,U_0 \sqcap U_1)$ by its range. The assertion is that the $k'$-dimension (as `Module.finrank`, hence $0$ in the infinite case) of the $H^0$ formed over $k'$ equals the $k$-dimension of the $H^0$ formed over $k$, and that the $H^1$ over $k'$ is subsingleton if and only if the $H^1$ over $k$ is.
--
--   This is flat base change for the two-chart alternating Čech complex of a locally trivial module, in the form needed to compare $h^0$ and the vanishing of $H^1$ on a fibre with their values after extension of the base field. It is used in the relative Picard arguments, in particular by the results computing $h^0$ and $H^1$ for fibres of Poincaré-type twists of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules)
    (hM : ∀ p : X, ∃ U : X.Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (k' : Type u) [Field k'] [Algebra k k'] :
    Module.finrank k'
        ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H0 =
      Module.finrank k (𝒱.sectionsOf x M).H0 ∧
    (Subsingleton ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H1 ↔
      Subsingleton (𝒱.sectionsOf x M).H1) := by sorry
