-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
-- name    : AutomorphicForm.setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/134863f9-7da4-51b6-88e7-8305e5f83ae1
-- title:
--   Nonvanishing weighted L² self-pairing over a slab fundamental domain
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$. Write $\mathrm{GL}_2(\mathbb{A}_K)$ for the general linear group of degree $2$ over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and for a unit $x$ of the adele ring let $\|x\|$ denote [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value at $x$ of the distributive Haar character of the adele ring, viewed as a real number. Let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, and assume $\Phi_0$ is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action of the range of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), i.e. the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ under the map induced by $K \to \mathbb{A}_K$, with respect to the Haar measure restricted to that slab. Let $\xi$ be a group homomorphism from the full subgroup of units of the adele ring to $\mathbb{C}^\times$, let $\sigma$ be real, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy: $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ (via its adelic image) and all $g$; $\varphi(z \cdot g) = \xi(z)\,\varphi(g)$ for every idele unit $z$, acting through the scalar matrix it defines; $\varphi$ is continuous; $\varphi$ lies in $L^2$ of the Haar measure restricted to $\Phi_0$; and $\varphi$ is not the zero function. Then $\int_{\Phi_0} \varphi(x)\,\overline{\varphi(x)}\,\|\det x\|^{-\sigma}\,dx \neq 0$, the real power being coerced into $\mathbb{C}$ and the integral taken with respect to `adelicGLHaar`.
--
--   This is the positivity (here: nonvanishing) of the weighted Petersson-type self-pairing of an automorphic function on a slab fundamental domain, the integrand being $|\varphi|^2\|\det\|^{-\sigma} \ge 0$. It serves as the denominator-nonvanishing input for the adelic $\mathrm{GL}_2$ spectral bookkeeping, being cited in the construction of elements of isotypic cuspidal subspaces, in the integrability and summability statements for convolution operators at principal level, and in the finiteness of cuspidal classes on a slab.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hφc : Continuous φ)
    (hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)) (hφ0 : φ ≠ 0) :
    ∫ x in Φ₀, φ x * conj (φ x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≠ 0 := by sorry
