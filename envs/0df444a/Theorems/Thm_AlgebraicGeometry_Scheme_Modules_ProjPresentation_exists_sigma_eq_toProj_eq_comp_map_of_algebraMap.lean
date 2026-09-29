-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/3ea7ab13-78e6-5768-8a35-0b47c312bc34
-- title:
--   Re-basing a P^N presentation along R → A
-- statement:
--   Let $R$ and $A$ be commutative rings with an $R$-algebra structure on $A$, let $X$ be a scheme with a morphism $f : X \to \operatorname{Spec} A$, let $M$ be an $\mathcal{O}_X$-module and let $N$ be a natural number. Suppose given a datum $\mathfrak{P}$ of type `M.ProjPresentation f N`, that is: global sections $\sigma_i \in \Gamma(M,\top)$ for $i \in \mathrm{Fin}(N+1)$; a morphism $\mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous submodule algebra of $A[x_0,\dots,x_N]$, composing with the structure morphism `ProjSpace.π` to give $f$; the condition that for every $i$ and every open $V$ of $X$ contained in the preimage of $D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot (\sigma_i|_V)$, is bijective; and the condition that for all $i,j$ the pullback along $\mathfrak{P}.\mathrm{toProj}$ of the section of $\mathcal{O}$ on $D_+(x_i)$ given by the ratio $x_j/x_i$ carries $\sigma_i|_{\mathfrak{P}.\mathrm{toProj}^{-1}D_+(x_i)}$ to $\sigma_j$ restricted to the same open. Then there exists a datum $\mathfrak{P}'$ of type `M.ProjPresentation (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) N`, i.e. for $X$ viewed over $\operatorname{Spec} R$ through $f$ followed by $\operatorname{Spec}$ of $R \to A$, whose sections satisfy $\mathfrak{P}'.\sigma_i = \mathfrak{P}.\sigma_i$ for all $i$ and whose morphism is $\mathfrak{P}.\mathrm{toProj}$ followed by `ProjSpace.map R A N`, the morphism $\operatorname{Proj}$ of $A[x_0,\dots,x_N] \to \operatorname{Proj}$ of $R[x_0,\dots,x_N]$ induced by coefficientwise application of $\operatorname{algebraMap} R A$.
--
--   This is the base-change compatibility of the classical description of morphisms to projective space by generating sections of a line bundle: the same $N+1$ sections present the composite $R$-morphism $X \to \mathbb{P}^N_A \to \mathbb{P}^N_R$. It is used where presentations produced over a quotient or extension ring must be read over the base ring, notably in the pullback lemmas for framed polarised abelian schemes and in the transfer of the section-basis condition along pullbacks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_sigma_eq_toProj_eq_comp_map_of_algebraMap.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_sigma_eq_toProj_eq_comp_map_of_algebraMap
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : M.ProjPresentation (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) N,
      (∀ i, 𝔓'.σ i = 𝔓.σ i) ∧ 𝔓'.toProj = 𝔓.toProj ≫ ProjSpace.map R A N := by sorry
