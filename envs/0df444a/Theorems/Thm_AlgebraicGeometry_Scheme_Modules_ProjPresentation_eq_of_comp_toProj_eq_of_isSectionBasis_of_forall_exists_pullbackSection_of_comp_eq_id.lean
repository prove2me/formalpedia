-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/46f6d382-f8a1-59d8-a8be-c39d2efe6358
-- title:
--   Separating sections force injectivity on k-points
-- statement:
--   Let $k$ be a field, $X$ a scheme, $f : X \to \operatorname{Spec} k$ a morphism, $\mathcal{N}$ a sheaf of $\mathcal{O}_X$-modules, $N$ a natural number, and let $\mathfrak{P}$ be a `ProjPresentation` of $\mathcal{N}$ relative to $f$ of size $N$: that is, a family $\sigma_0,\dots,\sigma_N$ of global sections of $\mathcal{N}$ together with a morphism $\mathfrak{P}.\mathrm{toProj} : X \to \operatorname{Proj} k[x_0,\dots,x_N]$ over $\operatorname{Spec} k$, such that on each open contained in the preimage of $D_+(x_i)$ multiplication by $\sigma_i$ is a bijection from functions to sections, and the pullback of the ratio $x_j/x_i$ on $D_+(x_i)$ carries $\sigma_i$ to $\sigma_j$ there. Assume (hypothesis `hσ`) that $\sigma$ is a section basis for $f$ and $\mathcal{N}$, i.e. the $k$-linear map sending $c : \mathrm{Fin}(N+1) \to k$ to $\sum_i f^\sharp(c_i)\,\sigma_i \in \Gamma(\mathcal{N},\top)$ is bijective; and assume that any two distinct sections $a \neq b$ of $f$ over $\operatorname{Spec} k$ are separated by some $s : \mathbf{1} \to \mathcal{N}$, meaning the pullback of $s$ along $a$ is zero while the pullback along $b$ is nonzero. Then for sections $a, b$ of $f$ with $a$ followed by $\mathfrak{P}.\mathrm{toProj}$ equal to $b$ followed by $\mathfrak{P}.\mathrm{toProj}$, one has $a = b$.
--
--   This is the step asserting that a complete linear system whose sections separate $k$-points gives a morphism to projective space that is injective on $k$-points (the $k$-point part of the classical criterion for a very ample system). It feeds the companion statement `eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection`, used in the construction of projective embeddings of the relevant schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id.lean

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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ)
    (hpt : ∀ a b : Spec (CommRingCat.of k) ⟶ X, a ≫ f = 𝟙 _ → b ≫ f = 𝟙 _ → a ≠ b →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝, Scheme.Modules.pullbackSection a s = 0 ∧ Scheme.Modules.pullbackSection b s ≠ 0)
    (a b : Spec (CommRingCat.of k) ⟶ X) (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a ≫ 𝔓.toProj = b ≫ 𝔓.toProj) :
    a = b := by sorry
