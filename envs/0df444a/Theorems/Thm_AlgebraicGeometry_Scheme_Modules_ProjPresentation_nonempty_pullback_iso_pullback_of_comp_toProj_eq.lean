-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_pullback_iso_pullback_of_comp_toProj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/24e4618a-c49e-55c8-8bb4-ca0d9d59bea9
-- title:
--   Morphisms agreeing on P^N have isomorphic pullbacks of a presented module
-- statement:
--   Let $R$ be a commutative ring, let $X$, $X'$ be schemes, let $f : X \to \operatorname{Spec} R$ be a morphism, let $\mathcal{N}$ be an $\mathcal{O}_X$-module and let $N$ be a natural number. Suppose given a `ProjPresentation` $\mathfrak{P}$ of $\mathcal{N}$ over $f$ of size $N$, that is: global sections $\sigma_i \in \Gamma(\mathcal{N}, X)$ for $i \in \{0,\dots,N\}$, a morphism $\varphi = \mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj}$ of the homogeneous coordinate ring $R[x_0,\dots,x_N]$ whose composite with the structural morphism `ProjSpace.π` is $f$, such that (i) for every $i$ and every open $V \subseteq \varphi^{-1}D_+(x_i)$ the map $\Gamma(X,V) \to \Gamma(\mathcal{N},V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and (ii) for all $i,j$ the section $\varphi^{\sharp}(x_j/x_i)$ over $\varphi^{-1}D_+(x_i)$ satisfies $\varphi^{\sharp}(x_j/x_i) \cdot \sigma_i|_{\varphi^{-1}D_+(x_i)} = \sigma_j|_{\varphi^{-1}D_+(x_i)}$. Let $T, S : X' \to X$ be morphisms with $T$ followed by $\varphi$ equal to $S$ followed by $\varphi$. Then the type of isomorphisms $T^{*}\mathcal{N} \cong S^{*}\mathcal{N}$ of $\mathcal{O}_{X'}$-modules is nonempty; no particular isomorphism is named.
--
--   The conditions on $\mathfrak{P}$ say that $\mathcal{N}$ is trivialised by $\sigma_i$ on $\varphi^{-1}D_+(x_i)$ with transition functions pulled back from the ratios $x_j/x_i$, so that $\mathcal{N}$ is the pullback along $\varphi$ of $\mathcal{O}(1)$ on $\mathbb{P}^N_R$; the statement is the resulting fact that $T^{*}\mathcal{N}$ depends only on the composite $\varphi \circ T$. It is used in the study of polarisations, in the two lemmas [`AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp`](thm.html#AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp) and its dual-number variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.nonempty_pullback_iso_pullback_of_comp_toProj_eq
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {𝓝 : X.Modules} {N : ℕ}
    (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (T S : X' ⟶ X) (h : T ≫ 𝔓.toProj = S ≫ 𝔓.toProj) :
    Nonempty ((Scheme.Modules.pullback T).obj 𝓝 ≅ (Scheme.Modules.pullback S).obj 𝓝) := by sorry
