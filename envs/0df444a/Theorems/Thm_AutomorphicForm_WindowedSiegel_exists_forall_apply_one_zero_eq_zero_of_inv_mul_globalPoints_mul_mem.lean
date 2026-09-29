-- Prove2me | Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
-- name    : AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/ec3fae15-b5d9-53ee-90b1-3f25b3481d8b
-- title:
--   Support lemma: high in the cusp forces γ₂₁=0
-- statement:
--   Let $F$ be a number field, and write $\mathbb{A}_F$ for the adele ring of $F$ over its ring of integers $\mathcal{O}_F$, with $\mathrm{GL}_2(\mathbb{A}_F)$ denoted [`AutomorphicForm.AdelicGL2 (𝓞 F) F`](def/AutomorphicForm_AdelicLsXi.html#L12). Let $C \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a compact subset. The assertion is the existence of a real number $T_0$ with the following property: for all $x, y \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite parts, i.e. the images `glFin` of $x$ and $y$ under the entrywise map induced by the projection $\mathbb{A}_F \to \mathbb{A}_F^{f}$ to the finite adeles, both lie in `finiteIntegralGL2 (𝓞 F) F`, the subgroup `finiteLevelZero (𝓞 F) F ⊤` consisting of those $g$ for which the predicate `IsLevelZeroMatrix (𝓞 F) F ⊤` holds of the underlying matrix of $g$ and of that of $g^{-1}$, and such that moreover $T_0 < \mathrm{archHeight}_F(x_\infty)$ and $T_0 < \mathrm{archHeight}_F(y_\infty)$, where $x_\infty$, $y_\infty$ are the images `glArch` of $x$, $y$ in $\mathrm{GL}_2$ of the infinite adeles and $$\mathrm{archHeight}_F(g) = \prod_{v \mid \infty} \big(\|\det g_v\| / \mathrm{rowNormSq}(g_v)\big)^{\,v.\mathrm{mult}}$$ is taken over the infinite places $v$ of $F$, with $g_v$ the component of $g$ at $v$ and `rowNormSq` the indicated norm quantity attached to a matrix: every $\gamma \in \mathrm{GL}_2(F)$ whose image under the diagonal embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A}_F)$ satisfies $x^{-1} \gamma y \in C$ has lower-left entry $\gamma_{10} = 0$.
--
--   This is the support lemma underlying Arthur's estimate of the automorphic kernel on a Siegel set in the rank-one case, where the only proper standard parabolic of $\mathrm{GL}_2$ is the Borel: high in the cusp, only upper-triangular rational elements contribute to a kernel built from a compactly supported test function. It is applied with $C$ the support of such a test function in the estimates of truncated and twisted adelic kernels over centre-cut Siegel-set translates, and in the counting of non-identity contributions to the kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem.lean

import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField

theorem AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mem
    (F : Type) [Field F] [NumberField F]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      NumberField.AdelicLevel.glFin (𝓞 F) F x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      NumberField.AdelicLevel.glFin (𝓞 F) F y ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F x) →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F y) →
      ∀ γ : GL (Fin 2) F,
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y ∈ C →
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by sorry
