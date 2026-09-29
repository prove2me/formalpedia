-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
-- name    : AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/09bc642e-97c7-55a6-8c59-15344ba0c9c0
-- title:
--   Propagation of SL₂(ℝ)-invariance through a cuspidal constituent
-- statement:
--   Let $F$ be a number field, let `pins : CarrierPins F` be a package of carrier data for $\mathrm{GL}_2$ over $F$ (a measurable space and measure on the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$, a subset $D$ of it, a subgroup $Z$ of the idele units, a family of subgroups indexed by the ideals of $\mathcal{O}_F$, a choice of element of the adelic group for each height-one prime, and a measurable space and measure on the adele ring), let $\xi : Z \to \mathbb{C}^{\times}$ be a character of that subgroup, and let $V$ be a $\mathbb{C}$-subspace of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$. Assume `IsCuspConstituent F pins ξ V`, that is: $V$ is contained in the submodule `cuspKFiniteSubmodule F pins ξ` and is stable under right translation by the finite-adelic subgroup, under right translation by the images of the groups `rowIsometrySubgroup₀ w.Completion` at every infinite place $w$, and under right convolution with factorizable test functions that are archimedean-bi-finite for some archimedean type family; moreover $V \neq 0$, and every subspace $W \le V$ with these same stability properties is $0$ or $V$. Let $w$ be a real infinite place, and let `archRealGLAt hw` denote the embedding $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{A}_F)$ obtained by transporting matrices along the ring isomorphism $\mathbb{R} \cong F_w$ and including at $w$. Suppose some $x_0 \in V$ is non-zero and satisfies $x_0(g\,\cdot\,\mathrm{archRealGLAt}(h)) = x_0(g)$ for all $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and all $h \in \mathrm{GL}_2(\mathbb{R})$ with $\det h = 1$. Then the same invariance holds for every $x \in V$: $x(g\,\cdot\,\mathrm{archRealGLAt}(h)) = x(g)$ for all $g$ and all $h$ of determinant one.
--
--   This is the elementary irreducibility argument that the subspace of $\mathrm{SL}_2(\mathbb{R})$-invariant vectors at a real place is itself stable under all the operations defining a cuspidal constituent, so that by minimality a single invariant vector forces invariance of the whole constituent. It is used in the analysis of the archimedean component of a cuspidal constituent, in the two results on the Casimir eigenvalue alternative (`casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex` and `...of_forall_isReal`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F pins ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by sorry
