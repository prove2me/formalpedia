-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/86d31aa2-ca68-5ba2-beb3-44202ab93d8c
-- title:
--   A projective presentation is determined by its sections
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ a sheaf of $\mathcal O_X$-modules on $X$, and $N$ a natural number (all in a single universe $u$). A datum of type `ProjPresentation` for $M$, $f$ and $N$ consists of: global sections $\sigma_i \in \Gamma(M,\top)$ indexed by $i \in \mathrm{Fin}(N+1)$; a morphism `toProj` from $X$ to $\operatorname{Proj}$ of the graded ring $R[x_0,\dots,x_N]$ with its homogeneous-component grading; the requirement that `toProj` followed by the structure morphism $\mathbb P^N_R \to \operatorname{Spec} R$ equals $f$; the condition that for every $i$ and every open $V \subseteq X$ contained in the preimage under `toProj` of the basic open $D_+(x_i)$, the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective, i.e. $\sigma_i$ frames $M$ there; and the relation that the pullback along `toProj` of the section $x_j/x_i$ of the affine chart $D_+(x_i)$, multiplied by the restriction of $\sigma_i$ to that preimage, equals the corresponding restriction of $\sigma_j$, for all $i,j$. The assertion is: given two such data $\mathfrak P$ and $\mathfrak Q$ whose sections agree, $\mathfrak P.\sigma_i = \mathfrak Q.\sigma_i$ for every $i \in \mathrm{Fin}(N+1)$, the two morphisms to $\mathbb P^N_R$ coincide: $\mathfrak P.\mathrm{toProj} = \mathfrak Q.\mathrm{toProj}$.
--
--   This is the uniqueness half of the classical description of morphisms to projective space by generating sections of a line bundle: the morphism is recovered from the frame data, so the only freedom in a projective presentation lies in the chosen sections. It is used in the treatment of framed polarised abelian schemes, for instance in identifying translates and in the pullback and reframing lemmas for such framings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 𝔔 : M.ProjPresentation f N) (h : ∀ i : Fin (N + 1), 𝔓.σ i = 𝔔.σ i) :
    𝔓.toProj = 𝔔.toProj := by sorry
