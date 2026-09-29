-- Prove2me | Theorems.Thm_AutomorphicForm_sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
-- name    : AutomorphicForm.sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/35e6a059-6b81-59e9-9a59-40830c5510c2
-- title:
--   σ-action preserves the adelic maximal compact and its Haar measure
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $D$ be an idelic Galois descent datum for $L/K$, i.e. a monoid homomorphism $D.\mathrm{act}$ from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of the adele ring $\mathbb{A}_L=\mathrm{AdeleRing}(\mathcal{O}_L,L)$ which is compatible with the structure map $L\to\mathbb{A}_L$ and continuous for each group element, and let $\sigma : L\simeq_{\mathrm{alg}[K]}L$. Write $\sigma_{\mathbb{A}}$ for [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14), the entrywise homomorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by the ring automorphism $D.\mathrm{act}\,\sigma$, and let $\mathbf{K}=$ [`AutomorphicForm.adelicMaximalCompact L`](def/AutomorphicForm_AdelicMaximalCompact.html#L19) be the subgroup of those $k\in\mathrm{GL}_2(\mathbb{A}_L)$ whose finite component `glFin` lies in `finiteIntegralGL2` (the level-$\top$ finite integral subgroup) and whose archimedean component at every infinite place $w$ of $L$ is a row isometry, meaning its determinant has norm $1$ and $(x,y)\mapsto (xk_{00}+yk_{10},\,xk_{01}+yk_{11})$ preserves $\|x\|^2+\|y\|^2$ over $w$-completion scalars. With the Borel measurable structure on $\mathrm{GL}_2(\mathbb{A}_L)$ and [`AutomorphicForm.maximalCompactHaar L`](def/AutomorphicForm_AdelicMaximalCompact.html#L208) the Haar measure of the top subgroup of $\mathbf{K}$, the assertion is twofold: first, $\sigma_{\mathbb{A}}$ maps every element of $\mathbf{K}$ back into $\mathbf{K}$; second, for every function $g:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$, with no measurability or integrability hypothesis, $\int_{\mathbf{K}}g(\sigma_{\mathbb{A}}k)\,dk=\int_{\mathbf{K}}g(k)\,dk$.
--
--   This is the standard fact that the Galois action on $\mathrm{GL}_2$ of the adeles stabilises the standard maximal compact subgroup (permuting the local factors over a given place of $K$) and hence preserves its Haar measure. It is used in the estimates of the Maass–Selberg and windowed Siegel machinery, feeding [`AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero`](thm.html#AutomorphicForm.exists_forall_norm_div_window_of_doubleCoset_apply_borel_mul_maximalCompact_ne_zero) and [`AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz`](thm.html#AutomorphicForm.exists_summable_dominant_rightConv_axis_family_sigma_maassSelberg_pairings_of_isSemiLocalFactorization_lipschitz).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.sigmaAdelicAct_mem_adelicMaximalCompact_and_integral_maximalCompactHaar_comp_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    (∀ k : AutomorphicForm.adelicMaximalCompact L,
        AutomorphicForm.sigmaAdelicAct K L D σ (k : AutomorphicForm.AdelicGL2 (𝓞 L) L) ∈
          AutomorphicForm.adelicMaximalCompact L) ∧
    ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ,
      (∫ k, g (AutomorphicForm.sigmaAdelicAct K L D σ (k : AutomorphicForm.AdelicGL2 (𝓞 L) L))
          ∂(AutomorphicForm.maximalCompactHaar L)) =
        ∫ k, g (k : AutomorphicForm.AdelicGL2 (𝓞 L) L) ∂(AutomorphicForm.maximalCompactHaar L) := by sorry
