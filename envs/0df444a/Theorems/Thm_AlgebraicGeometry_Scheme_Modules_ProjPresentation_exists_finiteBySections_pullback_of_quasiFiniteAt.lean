-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_finiteBySections_pullback_of_quasiFiniteAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5945c9c3-0692-50df-9920-28f90b5674d4
-- title:
--   Finiteness by sections after base change near a quasi-finite fibre
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $f\colon X \to \operatorname{Spec} R$ a proper morphism, let $M$ be a module on $X$ and $N$ a natural number, and let $\mathfrak{Q}$ be a `ProjPresentation` of $M$ over $f$ of size $N$: a family of global sections $\sigma_i \in \Gamma(M,\top)$ indexed by $i \in \mathrm{Fin}(N+1)$ together with a morphism $\mathfrak{Q}.\mathrm{toProj} \colon X \to \operatorname{Proj}$ of the graded ring of $R$-polynomials in $N+1$ variables, satisfying: composition with the structure morphism $\pi$ of $\mathbb{P}^N_R$ gives $f$; for each $i$ and each open $V \le \mathfrak{Q}.\mathrm{toProj}^{-1} D_+(x_i)$, the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective; and for all $i,j$, the pullback of the section $x_j/x_i$ of $D_+(x_i)$ acts on $\sigma_i$, restricted to $\mathfrak{Q}.\mathrm{toProj}^{-1} D_+(x_i)$, to give $\sigma_j$ restricted there. Assume $\mathfrak{p}$ is a prime of $R$ such that $\mathfrak{Q}.\mathrm{toProj}$ is quasi-finite at every point $x \in X$ with $f(x) = \mathfrak{p}$. Then there is $g \in R \setminus \mathfrak{p}$ such that for every commutative $R$-algebra $A$ in which the image of $g$ is a unit, and every scheme $X'$ with morphisms $p \colon X' \to X$ and $f' \colon X' \to \operatorname{Spec} A$ making the square over $\operatorname{Spec} A \to \operatorname{Spec} R$ a pullback, the module $p^{*}M$ is `FiniteBySections` over $f'$, that is, for some $N'$ it admits a `ProjPresentation` over $f'$ of size $N'$ whose associated morphism to $\mathbb{P}^{N'}_A$ is finite.
--
--   This is the spreading-out step which converts quasi-finiteness of a projective presentation along the single fibre over $\mathfrak{p}$ into finiteness of the presentation over a whole basic open neighbourhood of $\mathfrak{p}$, and hence over any base in which $g$ is inverted; it combines the openness of the quasi-finite locus with the fact that a proper locally quasi-finite morphism is finite. It feeds the construction of a base change over which a tensor power of $M$ becomes finite by sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_finiteBySections_pullback_of_quasiFiniteAt.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_finiteBySections_pullback_of_quasiFiniteAt
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} [IsProper f] {M : X.Modules} {N : ℕ}
    (𝔔 : M.ProjPresentation f N) (𝔭 : PrimeSpectrum R)
    (hqf : ∀ x : X, f x = 𝔭 → 𝔔.toProj.QuasiFiniteAt x) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) →
        ∀ {X' : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ Spec (.of A)),
          IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))) →
          Scheme.Modules.FiniteBySections ((Scheme.Modules.pullback p).obj M) f' := by sorry
