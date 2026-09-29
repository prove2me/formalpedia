-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f602e654-45c6-5db5-b2f9-a6aeb37879b3
-- title:
--   Integrability of the folded central–elliptic adelic GL₂ kernel
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta\in\mathbb{R}$ with $0<\alpha<\beta$. Write $G=\mathrm{GL}_2(\mathbb{A}_K)$ and let $S=\{g\mid \|\det g\|\in[\alpha,\beta]\}$ be the slab cut out by the idèle norm $\|\cdot\|$ of the determinant, the idèle norm being the value of the distributive Haar character of the adele ring. Let $\Phi_K\subseteq S$ be a fundamental domain, for the Haar measure `adelicGLHaar` of $G$ restricted to $S$, for the image of $\mathrm{GL}_2(K)\to G$ under the map induced by $K\to\mathbb{A}_K$. Equip the idèle group $\mathbb{A}_K^{\times}$ with a Borel measurable structure and a Haar measure $\nu$, and let $\Omega_K$ be a fundamental domain for the group of principal idèles, the image of $K^{\times}\to\mathbb{A}_K^{\times}$, with respect to $\nu$. Let $\xi_K$ be a homomorphism from the top subgroup of $\mathbb{A}_K^{\times}$ to $\mathbb{C}^{\times}$ whose associated $\mathbb{C}$-valued function on $\mathbb{A}_K^{\times}$ is continuous and which is trivial on the principal idèles, and let $f:G\to\mathbb{C}$ be continuous with compact support. For $x,y\in G$ put $K_{\mathrm{cen}}(x,y)=\sum_{\gamma}f(x^{-1}\gamma y)$, the finite-support sum over those $\gamma\in\mathrm{GL}_2(K)$ whose underlying matrix satisfies `IsCentralType`, and $K_{\mathrm{ell}}(x,y)$ the analogous sum over the $\gamma$ satisfying `IsEllipticType`. Then: first, for every $x\in G$ the function $z\mapsto \xi_K(z)\,\bigl(K_{\mathrm{cen}}(x,zx)+K_{\mathrm{ell}}(x,zx)\bigr)$, where $zx$ means the scalar matrix of $z$ times $x$, is integrable on $\Omega_K$ for $\nu$; second, the function $x\mapsto\int_{\Omega_K}\xi_K(z)\,\bigl(K_{\mathrm{cen}}(x,zx)+K_{\mathrm{ell}}(x,zx)\bigr)\,d\nu(z)$ is integrable on $\Phi_K$ for the Haar measure of $G$ itself (not restricted to the slab).
--
--   This is the integrability input needed to fold the central and elliptic contributions to the adelic $\mathrm{GL}_2$ kernel against a central character over a fundamental domain for the principal idèles, and then to integrate the folded kernel over a truncated (slab) fundamental domain for $\mathrm{GL}_2(K)$. It is used in the comparison of the central–elliptic part of the trace with its parabolic counterpart and in the computation of twisted cut traces of Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    AutomorphicForm.integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)))
      ΩK νZK) ∧
    IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => ∫ z in ΩK,
        ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x))
      ∂νZK) ΦK (adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
