-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
-- name    : AutomorphicForm.exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b6ea3ed6-f212-5e7d-a878-3c1133b65758
-- title:
--   Coarse geometric expansion of the truncated GL₂ kernel integral
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be real numbers, and let $\Phi_K\subseteq\mathrm{GL}_2(\mathbb A_K)$ be contained in the determinant slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the module of the translation action on $\mathbb A_K$, and be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on that slab, for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_K)$ restricted to the slab. Let $\nu_Z$ be a Haar measure on $\mathbb A_K^\times$ (taken with a Borel structure), $\Omega_K$ a fundamental domain for the image of $K^\times$ in $\mathbb A_K^\times$ with respect to $\nu_Z$, and $\xi$ a homomorphism from the full subgroup $\top\le\mathbb A_K^\times$ to $\mathbb C^\times$ whose associated $\mathbb C$-valued function is continuous and which is trivial on the image of $K^\times$. Let $f:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be factorizable, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ of compact support and given by a smooth function of the mixed-space matrix entries, and $f_{\mathrm{fin}}$ locally constant of compact support. Write $K_f(x,y)=\sum_{\gamma\in\mathrm{GL}_2(K)}f(x^{-1}\gamma y)$ for the adelic kernel and $K_f^{c},K_f^{e},K_f^{h},K_f^{u}$ for the same sums restricted to the central, elliptic, hyperbolic and unipotent cells of $\mathrm{GL}_2(K)$ (all sums are unconditional finite sums in the `finsum` sense). Truncation at parameter $T=e^{R}$ is $\Lambda^{T}\varphi(g)=\varphi(g)-\mathbf 1_{\{H(g)>T\}}\int \varphi(n(t)g)\,d\nu(t)$, with $H$ the adelic height `adelicHeight`, $n(t)$ the upper unipotent matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, and $\nu$ the measure recorded by `productionPinsOf`, namely the additive adelic Haar measure conditioned on the box `adelicBox K`. The assertion is that there is $R_0\in\mathbb R$ such that for every $R\ge R_0$ $$\int_{\Phi_0}\!\int_{\Omega_K}\xi(z)\,\Lambda^{e^R}\!\big[K_f(x,\cdot)\big](zx)\,d\nu_Z\,dx-\int_{\Phi_K}\!\int_{\Omega_K}\xi(z)\big(K^{c}_f+K^{e}_f\big)(x,zx)\,d\nu_Z\,dx$$ equals $$\int_{\Phi_0}\!\int_{\Omega_K}\xi(z)\Big(\big(K^{h}_f+K^{u}_f\big)(x,zx)-\mathbf 1_{\{H>e^R\}}\big(zx\big)\cdot\textstyle\int K_f(x,n(t)\,zx)\,d\nu(t)\Big)\,d\nu_Z\,dx,$$ where $\Phi_0=$ `canonicalTruncationDomain K α β` and $z$ acts through the central scalar embedding $\mathbb A_K^\times\to\mathrm{GL}_2(\mathbb A_K)$.
--
--   This is the coarse geometric expansion of the truncated kernel integral in the adelic trace formula for $\mathrm{GL}_2$ over a number field, folded against a central character: the kernel decomposes over the four conjugacy cells, the central and elliptic contributions are transferred from the canonical truncation domain to the given fundamental domain $\Phi_K$ of the determinant slab, and what remains is the parabolic (hyperbolic plus unipotent) term with the truncation's constant-term correction. It feeds the later analysis of the large-cutoff behaviour of the truncated integral, in particular the statements on the parabolic intercept, the twisted geometric remainder and the convergence of the truncated kernel integral as the cutoff grows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem
    AutomorphicForm.exists_forall_le_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
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
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (@AutomorphicForm.lambdaT _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
              (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
              (fun y => AutomorphicForm.adelicKernel K f x y)
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      (∫ x in ΦK, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
            AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
