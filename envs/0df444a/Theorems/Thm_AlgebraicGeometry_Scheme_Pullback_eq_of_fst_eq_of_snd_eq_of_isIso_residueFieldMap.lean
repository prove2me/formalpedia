-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
-- name    : AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/7359afd7-ff8c-54f3-80d5-3efca6961ed9
-- title:
--   Points of a fibre product with trivial residue extension
-- statement:
--   Let $X$, $Y$, $S$ be schemes (in a fixed universe), let $f \colon X \to S$ and $g \colon Y \to S$ be morphisms of schemes, and let $t_1, t_2$ be points of the underlying topological space of the pullback $X \times_S Y$. Assume that the two points have the same image under the first projection, $(\mathrm{pullback.fst}\ f\ g)(t_1) = (\mathrm{pullback.fst}\ f\ g)(t_2)$ in $X$, and the same image under the second projection, $(\mathrm{pullback.snd}\ f\ g)(t_1) = (\mathrm{pullback.snd}\ f\ g)(t_2)$ in $Y$. Assume further that, writing $x$ for the common image $(\mathrm{pullback.fst}\ f\ g)(t_2) \in X$, the residue field map induced by $f$ at $x$, namely $\kappa(f(x)) \to \kappa(x)$, is an isomorphism (this is an instance hypothesis). Then $t_1 = t_2$. Thus a point of $X \times_S Y$ is determined by its pair of projections as soon as the residue field extension of $f$ at the first projection is trivial; no hypothesis of finiteness, separatedness or flatness is imposed.
--
--   This is the standard description of the points of a fibre product of schemes over a pair of points with common image in $S$ — they form the spectrum of $\kappa(x) \otimes_{\kappa(s)} \kappa(y)$ — in the degenerate case $\kappa(s) \xrightarrow{\sim} \kappa(x)$, where that spectrum is a single point. It is used in the construction of Deligne–Rapoport style models of modular curves, where it yields injectivity of base-change maps over residually rational points, for instance in [`ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section`](thm.html#ModularCurve.DRModelPackageLevel.injective_crossingPt_of_exists_section) and in the existence statements for resolved model packages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Pullback_eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_of_snd_eq_of_isIso_residueFieldMap
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {t₁ t₂ : ↥(pullback f g)}
    (h₁ : (pullback.fst f g).base t₁ = (pullback.fst f g).base t₂)
    (h₂ : (pullback.snd f g).base t₁ = (pullback.snd f g).base t₂)
    [IsIso (f.residueFieldMap ((pullback.fst f g).base t₂))] :
    t₁ = t₂ := by sorry
