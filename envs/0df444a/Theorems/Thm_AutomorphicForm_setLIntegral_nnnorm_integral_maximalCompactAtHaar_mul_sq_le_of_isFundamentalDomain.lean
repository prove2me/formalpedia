-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
-- name    : AutomorphicForm.setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/062cf646-8d6d-59c8-a414-ec135959d31b
-- title:
--   Jensen bound for averaging over the archimedean maximal compact
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be real numbers, and write $G=\mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Let $\Phi_0\subseteq G$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action by left multiplication of the image of $\mathrm{GL}_2(K)$ under `globalPoints` (the map induced by $K\to\mathbb{A}_K$) with respect to the Haar measure restricted to the slab $\{g : \mathrm{ideleNorm}_K(\det g)\in[\alpha,\beta]\}$, where $\mathrm{ideleNorm}$ is the module of the idele, i.e. the value of `distribHaarChar` of $\mathbb{A}_K$, and assume in addition $\Phi_0$ is contained in that slab. Let $\mathcal K=$ `maximalCompactAt K ∅`, the subgroup of those $k$ whose finite part lies in `finiteIntegralGL2` and is trivial at every finite place (the $v$-component of the finite part is $1$ for all $v$) and whose archimedean component at each infinite place satisfies `IsRowIsometry`; give it the Haar measure `Measure.haarMeasure ⊤`. Let $\kappa:\mathcal K\to\mathbb{R}$ be continuous, nonnegative, with $\int\kappa=1$, and let $f:G\to\mathbb{C}$ be continuous and invariant under left multiplication by `globalPoints γ` for all $\gamma\in\mathrm{GL}_2(K)$. Then, as lower Lebesgue integrals in $[0,\infty]$, $\int_{\Phi_0}\bigl\|\int_{\mathcal K}\kappa(k)f(xk)\,dk\bigr\|^2dx\le\int_{\Phi_0}\|f(x)\|^2dx$.
--
--   This is the Jensen (Cauchy–Schwarz) contraction estimate saying that averaging a left $\mathrm{GL}_2(K)$-invariant continuous function against a probability density on the archimedean maximal compact subgroup does not increase its $L^2$-mass over a fundamental domain for the norm slab. It is used in the construction of $\mathcal K$-finite approximations, being cited by [`AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule) and by [`AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul`](thm.html#AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(maximalCompactAtHaar K ∅) = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfinv : ∀ (γ : GL (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), f (globalPoints (𝓞 K) K γ * x) = f x) :
    ∫⁻ x in Φ₀, (‖∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ∫⁻ x in Φ₀, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
