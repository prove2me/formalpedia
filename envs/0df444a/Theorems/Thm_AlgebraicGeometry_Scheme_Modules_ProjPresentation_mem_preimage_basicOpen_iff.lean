-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/5e45d283-0398-5591-a119-78c6b6b291a7
-- title:
--   Chart of a Proj presentation = locus where σᵢ is a local frame
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} R$ a morphism, $M$ a sheaf of modules on $X$, and $N$ a natural number. Let $\mathfrak{P}$ be a `ProjPresentation` of $M$ over $f$ of dimension $N$: that is, global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$, a morphism $\mathfrak{P}.\mathtt{toProj} : X \to \operatorname{Proj}$ of the graded algebra of homogeneous components of $R[x_0,\dots,x_N]$, whose composite with the structural projection $\mathtt{ProjSpace.\pi}$ is $f$, such that (i) for every $i$ and every open $V \subseteq \mathfrak{P}.\mathtt{toProj}^{-1}D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and (ii) over $\mathfrak{P}.\mathtt{toProj}^{-1}D_+(x_i)$ the pullback of the degree-zero fraction $x_j/x_i$ carries $\sigma_i$ to $\sigma_j$. Fix $i \in \{0,\dots,N\}$ and a point $x$ of $X$. Then $x$ lies in $\mathfrak{P}.\mathtt{toProj}^{-1}D_+(x_i)$ if and only if there is an open $U \ni x$ such that for every open $V \subseteq U$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective.
--
--   This identifies the $i$-th chart $\mathfrak{P}.\mathtt{toProj}^{-1}D_+(x_i)$ of a presentation of a morphism to projective space by sections of a module sheaf as precisely the largest open locus on which $\sigma_i$ is a local frame, the converse direction strengthening the `frame` axiom of `ProjPresentation` from a sufficient to a necessary condition. It is used in the comparison of presentations (rigidity of `toProj` given the sections), and in the finiteness-by-sections results for tensor powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_mem_preimage_basicOpen_iff.lean

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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.mem_preimage_basicOpen_iff
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (i : Fin (N + 1)) (x : X) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i) : Γ(M, V)) := by sorry
