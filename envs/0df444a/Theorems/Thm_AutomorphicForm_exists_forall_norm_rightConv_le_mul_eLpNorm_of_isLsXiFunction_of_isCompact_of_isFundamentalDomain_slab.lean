-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/607e72d2-4f0e-5f96-bad3-1727a3fa1059
-- title:
--   Right convolution bounds L² of a slab domain by sup on compacta
-- statement:
--   Let $K$ be a number field, with $\mathrm{GL}_2(\mathbb{A}_K)$ carried by [`AutomorphicForm.AdelicGL2 (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L12) and equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`. Fix reals $0<\alpha<\beta$ and a set $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ contained in the slab $\{g:\ \lVert\det g\rVert\in[\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is `ideleNorm`, the value of the distributive Haar character of the adele ring at an idele; assume $\Phi_0$ is a measure-theoretic fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ under the entrywise map `globalPoints` on the Haar measure restricted to that slab. Fix a group homomorphism $\xi$ from the full subgroup of ideles $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ (no continuity or unitarity assumed), a continuous compactly supported $g:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, and a compact set $C$. Then there is a real $M$ such that for every continuous $u:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying $u(\gamma h)=u(h)$ for all $\gamma\in\mathrm{GL}_2(K)$ and $u(zI\cdot h)=\xi(z)u(h)$ for all ideles $z$, and lying in $L^2$ of the Haar measure restricted to $\Phi_0$, one has $\bigl\lvert\int u(xy)g(y)\,dy\bigr\rvert\le M\cdot\lVert u\rVert_{L^2(\Phi_0)}$ for all $x\in C$, the norm being the real value of the $L^2$-seminorm.
--
--   This is the elementary half of Godement's boundedness estimate: right convolution with a continuous compactly supported kernel maps $L^2$ of a fundamental domain for $\mathrm{GL}_2(K)$ in a determinant slab into functions bounded uniformly on compact sets, with a constant depending only on the kernel and the compact set, not on the automorphic function. It feeds the trace-type estimates for sums over orthonormal families, being used in the proof of [`AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.forall_isCompact_exists_tsum_norm_finsum_twistedConvOp_mul_conj_le_of_orthonormal_of_isFundamentalDomain_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ M : ℝ, ∀ u : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ,
      AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u → Continuous u →
        MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ x ∈ C, ‖AutomorphicForm.rightConv K u g x‖ ≤
            M * (eLpNorm u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by sorry
