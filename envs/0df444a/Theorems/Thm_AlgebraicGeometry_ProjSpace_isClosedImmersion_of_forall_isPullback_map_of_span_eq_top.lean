-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
-- name    : AlgebraicGeometry.ProjSpace.isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/c83c1daa-dc26-525a-8f76-1110864db2cd
-- title:
--   Closed immersion into P^N_S detected on a principal cover
-- statement:
--   Let $S$ be a commutative ring and let $r_1,\dots,r_k$ be elements of $S$ indexed by `Fin k` whose range generates the unit ideal, $\mathrm{span}(\mathrm{range}\,r)=\top$. For each $i$ let $B_i$ be a commutative $S$-algebra which is a localisation of $S$ away from $r_i$. Fix $N\in\mathbb{N}$, and write $\mathbb{P}^N_R$ for $\operatorname{Proj}$ of the graded ring of homogeneous components of $R[x_0,\dots,x_N]$, i.e. `MvPolynomial.homogeneousSubmodule (Fin (N+1)) R`. Let $X$ be a scheme with a morphism $t\colon X \to \mathbb{P}^N_S$, and for each $i$ let $X'_i$ be a scheme with morphisms $t'_i\colon X'_i \to \mathbb{P}^N_{B_i}$ and $g_i \colon X'_i \to X$ such that the square with sides $g_i$ followed by $t$ and $t'_i$ followed by `ProjSpace.map S (B i) N` (the morphism $\mathbb{P}^N_{B_i}\to\mathbb{P}^N_S$ induced by $\operatorname{Proj}$ of coefficientwise extension of scalars along $S \to B_i$) is cartesian, so that $X'_i \cong X\times_{\mathbb{P}^N_S}\mathbb{P}^N_{B_i}$ with $t'_i$ the second projection. If every $t'_i$ is a closed immersion, then $t$ is a closed immersion.
--
--   This is the statement that being a closed immersion into projective space over $S$ is local on the base for a cover of $\operatorname{Spec} S$ by basic open sets $D(r_i)$, the $\mathbb{P}^N$ form of the Zariski-local nature of closed immersions at the target. It is used by [`AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away`](thm.html#AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_forall_isPullback_away) to check, locally on the base, that the sections of an invertible module define a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_isClosedImmersion_of_forall_isPullback_map_of_span_eq_top.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isClosedImmersion_of_forall_isPullback_map_of_span_eq_top
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    (N : ℕ) {X : Scheme.{u}} (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S))
    {X' : Fin k → Scheme.{u}} (t' : ∀ i, X' i ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (B i)))
    (g : ∀ i, X' i ⟶ X) (hsq : ∀ i, IsPullback (g i) (t' i) t (ProjSpace.map S (B i) N))
    (h : ∀ i, IsClosedImmersion (t' i)) :
    IsClosedImmersion t := by sorry
