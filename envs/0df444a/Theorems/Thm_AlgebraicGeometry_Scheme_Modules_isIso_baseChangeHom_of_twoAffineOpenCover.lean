-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/91e5b869-bab9-5865-8530-ba4c7d91e0b7
-- title:
--   Base change in degree zero, two-chart Čech form
-- statement:
--   Let $A$ be a Noetherian commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec}A$ a flat morphism; let $\mathcal V$ be a two-chart affine open cover of $X$, that is, a pair of opens $U_0,U_1$ with $U_0\sqcup U_1$ (as a join of opens) equal to $\top$ and with $U_0$, $U_1$ and $U_0\cap U_1$ all affine; and let $F$ be an $\mathcal O_X$-module. Assume: (i) every point of $X$ has an open neighbourhood $V$ on which the restriction of $F$ along $V\hookrightarrow X$ is isomorphic to the unit sheaf of modules of $V$, i.e. to $\mathcal O_V$; (ii) both $A$-modules attached to the two-term Čech complex $d=(-r_0)\sqcup r_1\colon \Gamma(F,U_0)\times\Gamma(F,U_1)\to\Gamma(F,U_0\cap U_1)$ of $F$ on $\mathcal V$ over $\pi$, namely $\ker d$ and $\operatorname{coker} d$, are finite over $A$; (iii) for every field $K$ equipped with an $A$-algebra structure, the corresponding $\operatorname{coker}$ of the two-term Čech complex on the pulled-back two-chart cover of $X\times_{\operatorname{Spec}A}\operatorname{Spec}K$, for the module pulled back along the first projection and over the second projection, is a subsingleton. Then for every $A$-algebra $A'$, every scheme $X'$, every $\pi'\colon X'\to\operatorname{Spec}A'$ and $g'\colon X'\to X$ making the square with $\pi$ and $\operatorname{Spec}A'\to\operatorname{Spec}A$ cartesian, the base-change morphism $\psi^*\pi_*F\to\pi'_*g'^*F$ (the mate, under the pullback–pushforward adjunctions, of the pullback two-square of the commuting square) is an isomorphism.
--
--   This is cohomology and base change in degree $0$ — in the form of EGA III 7.7.5 ff., Hartshorne III.12.11 and Mumford's criterion in §5 of Abelian Varieties — specialised to an affine Noetherian base, a two-chart Čech computation of cohomology, and arbitrary (not necessarily flat) base change $A\to A'$, for modules that are Zariski-locally isomorphic to the structure sheaf. It underlies the relative Picard results [`AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre), [`AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover`](thm.html#AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre_of_twoAffineOpenCover) and [`AlgebraicGeometry.RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_twoAffineOpenCover
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A)) [Flat π]
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H0 ∧ Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (pullback.snd π (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (pullback.fst π (Scheme.TwoAffineOpenCover.specMap A K))).obj F)).H1)
    (A' : Type u) [CommRing A'] [Algebra A A'] {X' : Scheme.{u}} (π' : X' ⟶ Spec (.of A')) (g' : X' ⟶ X)
    (hcart : IsPullback g' π' π (Scheme.TwoAffineOpenCover.specMap A A')) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) := by sorry
