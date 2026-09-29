-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.injective_toProj_of_forall_exists_eq_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/c3cb31ce-6de7-5197-91dd-34fc63d3fcf1
-- title:
--   Injectivity on points transfers between Proj presentations
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ a module over $X$, and $N, N'$ natural numbers. Suppose given two presentations $\mathfrak P$ and $\mathfrak Q$ of $M$ over $f$, of sizes $N$ and $N'$ respectively: such a datum of size $N$ consists of global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$ together with a morphism $\mathfrak P.\mathtt{toProj} : X \to \operatorname{Proj}$ of the graded ring $R[X_0,\dots,X_N]$ whose composite with the structure morphism $\mathrm{ProjSpace.\pi}\,R\,N$ is $f$, such that (frame) for every $i$ and every open $V \subseteq \mathfrak P.\mathtt{toProj}^{-1}D_+(X_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and (ratio) for all $i,j$ the pullback along $\mathfrak P.\mathtt{toProj}$ of the section of $\operatorname{Proj}$ over $D_+(X_i)$ attached to $X_j/X_i$ multiplied by $\sigma_i$ restricted to $\mathfrak P.\mathtt{toProj}^{-1}D_+(X_i)$ equals $\sigma_j$ restricted to that open. Assume that the map on underlying topological spaces of $\mathfrak P.\mathtt{toProj}$ is injective, and that each section of $\mathfrak P$ is an $R$-linear combination of the sections of $\mathfrak Q$: for every $i$ there are $c_j \in R$ with $\mathfrak P.\sigma_i = \sum_j (f^{\sharp}(c_j)) \cdot \mathfrak Q.\sigma_j$, the scalars being transported to $\Gamma(X,\top)$ along $f$ via the isomorphism $\Gamma \circ \operatorname{Spec} \cong \mathrm{id}$. Then the map on underlying topological spaces of $\mathfrak Q.\mathtt{toProj}$ is also injective.
--
--   This is the comparison step in the classical theory of maps to projective space determined by generating sections (as in Hartshorne II.7.1 or EGA II 4.2): a topological property of the induced morphism to $\mathbb P^N_R$ is inherited by a second presentation whose sections span those of the first over $R$. It is used in the proof that the morphism attached to such a presentation is a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.injective_toProj_of_forall_exists_eq_sum_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') (hinj : Function.Injective 𝔓.toProj.base)
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    Function.Injective 𝔔.toProj.base := by sorry
