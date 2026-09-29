-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/5c1af421-c100-558a-8b56-0bcacf5b892e
-- title:
--   Adjoint of right convolution on a slab fundamental domain
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be real numbers, and write $\mathrm{GL}_2(\mathbb{A}_K)$ for [`AutomorphicForm.AdelicGL2 growth`](def/AutomorphicForm_AdelicLsXi.html#L12), i.e. the group of invertible $2\times 2$ matrices over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`; here $\|\cdot\|$ denotes [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of the adele ring at an idele, viewed as a real number. Let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, and assume $\Phi_0$ is a fundamental domain, in the measure-theoretic sense of `IsFundamentalDomain`, for the action of the image of $\mathrm{GL}_2(K)$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) (the map induced by $K \to \mathbb{A}_K$) on the Haar measure restricted to that slab. Let $\xi$ be a group homomorphism from the full subgroup $\top$ of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ with $\|\xi(z)\| = \|z\|^{\sigma}$ for a fixed real $\sigma$ and all $z$. Let $u,v : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, square-integrable for the Haar measure restricted to $\Phi_0$, and satisfy `IsLsXiFunction` for $\top$ and $\xi$: invariance $u(\gamma g) = u(g)$ for $\gamma \in \mathrm{GL}_2(K)$ (embedded via `globalPoints`), and $u(z\cdot g) = \xi(z)\,u(g)$ for central scalar matrices $z \in \mathbb{A}_K^\times$, likewise for $v$. Let $g$ be continuous with compact support. Then, with $(\mathrm{rightConv}\,\varphi\,f)(x) = \int \varphi(xy) f(y)\,dy$ against the Haar measure, $$\int_{\Phi_0} (\mathrm{rightConv}\,u\,g)(x)\,\overline{v(x)}\,dx = \int_{\Phi_0} u(x)\,\overline{(\mathrm{rightConv}\,v\,g^{\flat})(x)}\,dx,$$ where $g^{\flat}(y) = \overline{g(y^{-1})}\,\|\det y\|^{-\sigma}$.
--
--   This is the adjointness relation $R(g)^{*} = R(g^{\flat})$ for the right convolution operators acting on $\xi$-covariant automorphic functions, taken with respect to the unweighted Hermitian pairing $\langle a,b\rangle = \int_{\Phi_0} a\,\overline{b}$ on a slab fundamental domain. It is used in the construction of elements of isotypic cuspidal submodules with prescribed convolution values, and in the uniform bounds on sums of convolution operators applied to an orthonormal family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hu : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x in Φ₀, AutomorphicForm.rightConv K u g x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) x)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
