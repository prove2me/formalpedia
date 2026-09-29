-- Prove2me | Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
-- name    : AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/fcc1abb9-98ac-5e58-90e9-11726631f898
-- title:
--   Finiteness of Haar measure of a slab fundamental domain
-- statement:
--   Let $K$ be a number field, and let $\mathbb{A}_K$ denote its adele ring, with $\mathrm{GL}_2(\mathbb{A}_K)$ the general linear group of $2\times 2$ matrices over $\mathbb{A}_K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Write $\|\cdot\|$ for the idele norm, defined on $\mathbb{A}_K^{\times}$ as the value of the distributive Haar character of $\mathbb{A}_K$ at the given unit, viewed as a real number, and let $\Gamma$ be the image of the homomorphism $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A}_K)$ induced entrywise by the structure map $K\to\mathbb{A}_K$. Given reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$, put $S=\{g\in\mathrm{GL}_2(\mathbb{A}_K) : \|\det g\|\in[\alpha,\beta]\}$, and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a set which is a measure-theoretic fundamental domain, in the sense of Mathlib's `IsFundamentalDomain`, for the action of $\Gamma$ with respect to the Haar measure restricted to $S$. The conclusion is that the Haar measure of $\Phi_0\cap S$ is finite, i.e. strictly less than $\top$ in $[0,\infty]$.
--
--   This is the finiteness of the volume of $\mathrm{GL}_2(K)\backslash\mathrm{GL}_2(\mathbb{A}_K)^{[\alpha,\beta]}$, i.e. the adelic form of the Borel–Harish-Chandra / Godement finite-volume theorem for $\mathrm{GL}_2$ over a number field, in the special shape of a determinant slab. It makes the carrier of the $L^2$ theory on a slab fundamental domain a finite measure space, and is used throughout the analytic treatment of the cuspidal spectrum, in particular for the estimates on tails needed for compactness of smoothing operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    adelicGLHaar (Fin 2) (𝓞 K) K
        (Φ₀ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) < ⊤ := by sorry
