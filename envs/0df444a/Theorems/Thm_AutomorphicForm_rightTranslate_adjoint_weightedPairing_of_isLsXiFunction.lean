-- Prove2me | Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
-- name    : AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ecc133a3-57f7-520c-8159-458d7887875f
-- title:
--   Right translation is adjoint for the weighted Petersson pairing
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be real with $0<\alpha$, and work with the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ for the Borel structure `glBorel`, where $\mathbb{A}_K$ is the adèle ring of $K$. Write $\|\cdot\|$ for `ideleNorm`, the value of the distributive Haar character of $\mathbb{A}_K$ at an idèle, viewed as a real number. Let $\Phi_0$ be a subset of the slab $\{g:\|\det g\|\in[\alpha,\beta]\}$ which is a fundamental domain, in the sense of `IsFundamentalDomain`, for the image subgroup of $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A}_K)$ induced by $K\to\mathbb{A}_K$, relative to the Haar measure restricted to that slab. Let $\xi$ be a homomorphism from the full unit group $\mathbb{A}_K^\times$ (as the top subgroup) to $\mathbb{C}^\times$ and $\sigma$ real with $\|\xi(z)\|_{\mathbb{C}}=\|z\|^{\sigma}$ for all $z$. Let $u,v:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, each satisfying `IsLsXiFunction`, i.e. invariance $u(\gamma g)=u(g)$ under the image of $\gamma\in\mathrm{GL}_2(K)$ and $u(\mathrm{diag}(z,z)g)=\xi(z)u(g)$ for $z\in\mathbb{A}_K^\times$, and each in $L^2$ of the Haar measure restricted to $\Phi_0$. Then for every $y\in\mathrm{GL}_2(\mathbb{A}_K)$: the functions $x\mapsto u(xy)$ and $x\mapsto v(xy^{-1})$ lie in $L^2(\Phi_0)$, and $$\int_{\Phi_0}u(xy)\,\overline{v(x)}\,\|\det x\|^{-\sigma}\,dx=\|\det y\|^{\sigma}\int_{\Phi_0}u(x)\,\overline{v(xy^{-1})}\,\|\det x\|^{-\sigma}\,dx.$$
--
--   This is the transformation law of the weighted Petersson pairing $\langle a,b\rangle=\int_{\Phi_0}a\,\overline{b}\,\|\det\|^{-\sigma}$ on functions with central character $\xi$ of modulus $\|\cdot\|^{\sigma}$: right translation by $y$ is adjoint to right translation by $y^{-1}$ up to the factor $\|\det y\|^{\sigma}$, the weight being what compensates for a non-unitary central character. It underlies the study of right translation and right convolution on the cuspidal spectrum, and is used by the results on lifting right translates and bounding right convolutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
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
    (y : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => v (x * y⁻¹)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, u (x * y) * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
