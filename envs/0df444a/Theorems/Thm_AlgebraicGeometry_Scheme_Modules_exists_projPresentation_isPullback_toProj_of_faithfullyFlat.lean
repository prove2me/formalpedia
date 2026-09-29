-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat
-- name    : AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isPullback_toProj_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/ca34c2ce-e729-5f3e-a88a-ad54e5ac27b8
-- title:
--   Descending a projective presentation by sections along faithfully flat base change
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra that is faithfully flat as an $S$-module, let $X, X'$ be schemes, let $f : X \to \operatorname{Spec} S$ be quasi-compact and separated, let $f' : X' \to \operatorname{Spec} S'$ and $c : X' \to X$ be morphisms, and assume the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of $S \to S'$ is cartesian. Let $L$ be a module on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the restriction of $L$ to $U$ isomorphic to the unit module on $U$, let $L'$ be a module on $X'$ and $e : c^{*}L \cong L'$ an isomorphism. Finally let $\mathfrak{Q}$ be a `ProjPresentation` of $L'$ relative to $f'$ with $M+1$ sections, that is: sections $\mathfrak{Q}.\sigma_j \in \Gamma(L', \top)$ for $j \in \mathrm{Fin}(M+1)$, a morphism $\mathfrak{Q}.\mathrm{toProj} : X' \to \operatorname{Proj}$ of the algebra of homogeneous polynomials in $M+1$ variables over $S'$ composing with the structure morphism to $f'$, such that on every open $V$ contained in the preimage of the basic open set $D(X_j)$ the map $g \mapsto g \cdot \mathfrak{Q}.\sigma_j|_V$ is a bijection $\Gamma(X', V) \to \Gamma(L', V)$, and such that the pullback of the ratio $X_k/X_j$ carries $\sigma_j$ to $\sigma_k$ over $D(X_j)$. Then there exist $N$, a `ProjPresentation` $\mathfrak{P}$ of $L$ relative to $f$ with $N+1$ sections and a `ProjPresentation` $\mathfrak{P}'$ of $L'$ relative to $f'$ with $N+1$ sections such that the square formed by $c$, $\mathfrak{P}'.\mathrm{toProj}$, $\mathfrak{P}.\mathrm{toProj}$ and the map $\mathbb{P}^N_{S'} \to \mathbb{P}^N_{S}$ induced by $S \to S'$ on coefficients is cartesian, and such that for every $j$ there are scalars $a_l \in S'$ with $\mathfrak{Q}.\sigma_j = \sum_l (f'^{\sharp} a_l) \cdot \mathfrak{P}'.\sigma_l$, the scalars acting through the global sections of $f'$.
--
--   This is the descent step for presentations of a scheme as a subscheme of projective space by sections of an invertible module: a presentation available only after faithfully flat base change $S \to S'$ is dominated, up to $S'$-linear combinations of sections, by the base change of a presentation defined over $S$. It is used in the construction of a closed immersion by sections over the base ring via faithfully flat descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_isPullback_toProj_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_isPullback_toProj_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {M : ℕ} (𝔔 : Scheme.Modules.ProjPresentation L' f' M) :
    ∃ (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation L f N) (𝔓' : Scheme.Modules.ProjPresentation L' f' N),
      IsPullback c 𝔓'.toProj 𝔓.toProj (ProjSpace.map S S' N) ∧
      ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S',
        𝔔.σ j = ∑ l, ((f'.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S')).inv.hom (a l))) • 𝔓'.σ l := by sorry
