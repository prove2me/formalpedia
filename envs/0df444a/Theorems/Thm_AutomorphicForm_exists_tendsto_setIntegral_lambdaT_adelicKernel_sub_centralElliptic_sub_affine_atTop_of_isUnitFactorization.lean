-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
-- name    : AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/2fb90977-454a-598a-93d5-adab35003cf0
-- title:
--   Asymptotically affine truncated parabolic term, unit-factorizable f
-- statement:
--   Let $K$ be a number field and $0<\alpha<\beta$ real. Let $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be contained in the determinant slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character, and assume $\Phi_K$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ with respect to the adelic Haar measure restricted to that slab. On the idele group fix a Borel measurable structure, a Haar measure $\nu_{Z,K}$, and a fundamental domain $\Omega_K$ for the image of $K^\times$. Let $\xi$ be a homomorphism from the full idele unit group to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$. Let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ admit a unit factorization: there are a finite set $S$ of finite places, $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles which is smooth in the matrix entries and compactly supported, $f_{\mathrm{fin}}$ locally constant and compactly supported, and local functions $f_v$ ($v\in S$) locally constant and compactly supported, such that $f_{\mathrm{fin}}(h)=\prod_{v\in S}f_v(h_v)$ whenever $h_v$ is integral at every $v\notin S$, $f_{\mathrm{fin}}(h)=0$ as soon as $h_v$ fails to be integral at some $v\notin S$, and $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$. Then there exist $\nu,\mu\in\mathbb{C}$ such that, as $R\to+\infty$, $$\int_{\Phi_0}\int_{\Omega_K}\xi(z)\,\bigl(\Lambda^{e^R}K_f(x,\cdot)\bigr)(z\,x)\,d\nu_{Z,K}(z)\,dx-\int_{\Phi_K}\int_{\Omega_K}\xi(z)\bigl(K_f^{\mathrm{cent}}+K_f^{\mathrm{ell}}\bigr)(x,z\,x)\,d\nu_{Z,K}(z)\,dx-(R\nu+\mu)\to 0,$$ where $\Phi_0$ is the canonical truncation domain attached to $(K,\alpha,\beta)$, $z$ acts through the central scalar embedding of the ideles, $K_f(x,y)=\sum_{\gamma\in\mathrm{GL}_2(K)}f(x^{-1}\gamma y)$, the central and elliptic parts $K_f^{\mathrm{cent}}$, $K_f^{\mathrm{ell}}$ are the same sums restricted to the $\gamma$ whose matrix is of central, respectively elliptic, type, and $\Lambda^{T}\varphi(g)=\varphi(g)-\mathbf 1_{\{\text{adelic height}>T\}}(g)\int \varphi(u(t)g)\,dt$ with $u(t)$ the upper unipotent matrix and $dt$ the additive adelic Haar measure conditioned on the adelic box (a fundamental domain for the Minkowski lattice at the infinite places times the integral finite adeles).
--
--   This is the unit-factorizable case of the statement that the truncated parabolic contribution to the $\xi$-twisted $\mathrm{GL}_2$ trace formula over $K$ differs from an affine function $R\nu+\mu$ of the logarithmic truncation parameter by a quantity tending to $0$, the truncated spectral side minus the central and elliptic terms being what remains. It feeds the comparison of parabolic terms along Hecke words, being cited in the derivation of the uniform intercept identity for parabolic terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization.lean

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

theorem AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization
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
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hff : ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
      (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
      (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
      AutomorphicForm.IsUnitFactorization K S f fa ff fS) :
    ∃ ν μ : ℂ, Filter.Tendsto (fun R : ℝ =>
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
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * ν + μ)) Filter.atTop (nhds 0) := by sorry
