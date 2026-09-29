-- Prove2me | Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
-- name    : AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c1dd1bd7-4001-520c-b32f-c5dae3d8bc83
-- title:
--   Adjointness of right convolution for the weighted Petersson pairing
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$, and write $\|\det g\|$ for the value at $\det g$ of the module character [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) (the `distribHaarChar` of the adele ring of $K$). Let $\Phi_0$ be a subset of the slab $\{g \in \mathrm{GL}_2(\mathbb{A}_K) : \|\det g\| \in [\alpha,\beta]\}$ which is a fundamental domain, for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that slab, for the image subgroup $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$. Let $\xi : \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a homomorphism on the full centre with $|\xi(z)| = \|z\|^{\sigma}$ for a real $\sigma$, and let $u,v : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, left invariant under $\mathrm{GL}_2(K)$ and satisfying $u(zg)=\xi(z)u(g)$ for central $z$ (likewise $v$), and of class $L^2$ for Haar measure restricted to $\Phi_0$. Let $g$ be continuous with compact support, and put $g^{\flat}(y) = \overline{g(y^{-1})}\,\|\det y\|^{-\sigma}$. With $(\varphi * f)(x) = \int \varphi(xy) f(y)\,dy$ denoting `rightConv`, the conclusion asserts three things: $u * g$ and $v * g^{\flat}$ are again $L^2$ on $\Phi_0$, and $\int_{\Phi_0} (u*g)(x)\,\overline{v(x)}\,\|\det x\|^{-\sigma} = \int_{\Phi_0} u(x)\,\overline{(v*g^{\flat})(x)}\,\|\det x\|^{-\sigma}$.
--
--   This is the adjoint formula for the right convolution operator $R(g)$ acting on automorphic functions with central character $\xi$ of modulus $\|\cdot\|^{\sigma}$: for the Petersson pairing weighted by $\|\det\|^{-\sigma}$, so as to be defined on functions of non-unitary central character, the adjoint of $R(g)$ is $R(g^{\flat})$, reducing for $\sigma = 0$ to the classical $R(g)^{*} = R(g^{*})$ with $g^{*}(y)=\overline{g(y^{-1})}$. It is used in the analysis of the cuspidal spectrum, for instance in constructing lifts and norm bounds for right convolutions and in showing that right convolution preserves the cuspidal submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
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
    MemLp (AutomorphicForm.rightConv K u g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, AutomorphicForm.rightConv K u g x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (AutomorphicForm.rightConv K v (fun y => conj (g y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
