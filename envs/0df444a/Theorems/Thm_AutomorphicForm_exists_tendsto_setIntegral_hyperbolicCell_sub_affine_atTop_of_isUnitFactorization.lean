-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
-- name    : AutomorphicForm.exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f71d1c31-032b-5a07-b4c2-8adf8e0055d1
-- title:
--   Affine asymptotics of the truncated hyperbolic term, unit factorisation
-- statement:
--   Let $K$ be a number field and $0 < \alpha < \beta$ real. Let $\Phi_K \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be contained in the slab $\{g : \lVert\det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the idele norm given by the module of the Haar character of $\mathbb{A}_K$, and be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on the restriction of the adelic Haar measure `adelicGLHaar` to that slab. Let $\nu_{Z}$ be a Haar measure on $\mathbb{A}_K^\times$ (with a Borel measurable structure) and $\Omega_K$ a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ for $\nu_Z$. Let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous as a function on $\mathbb{A}_K^\times$ and trivial on principal ideles. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ admit a unit factorisation: there are a finite set $S$ of finite places, an archimedean factor $f_\infty$ which is a compactly supported function of the matrix entries given by a smooth function on the mixed space, a locally constant compactly supported finite factor $f_{\mathrm{fin}}$, and local factors $f_v$ (locally constant with compact support for $v \in S$) such that $f_{\mathrm{fin}}(h) = \prod_{v \in S} f_v(h_v)$ when all components of $h$ outside $S$ lie in the integral set, $f_{\mathrm{fin}}(h) = 0$ when some component outside $S$ fails to, and $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$. Then there exist $a, b \in \mathbb{C}$ such that, as $R \to +\infty$, $$\int_{\mathcal T_{\alpha,\beta}} \int_{\Omega_K} \xi(z)\Bigl( K^{\mathrm{hyp}}_f(x, zx) - \mathbf 1_{\{\,\mathrm{ht} > e^{R}\,\}}(zx)\, C_x(zx) \Bigr)\, d\nu_Z(z)\, dx \; - \; (R\,a + b) \;\longrightarrow\; 0,$$ where $\mathcal T_{\alpha,\beta}$ is the canonical truncation domain `canonicalTruncationDomain K α β`, the integration in $x$ is against `adelicGLHaar`, $z$ acts through the central scalar matrix, $K^{\mathrm{hyp}}_f(x,y) = \sum^{f}_{\gamma} f(x^{-1}\gamma y)$ is the finite sum over the $\gamma \in \mathrm{GL}_2(K)$ of hyperbolic type, $\mathrm{ht}$ is the adelic height (the product of the archimedean and finite local heights), and $C_x(g) = \int \bigl(\sum^{f}_{\gamma} f(x^{-1}\gamma\, u(t) g)\bigr)\, d\nu(t)$ is the unipotent integral of the sum over $\gamma \in \mathrm{GL}_2(K)$ with lower-left entry $0$ and diagonal ratio $\gamma_{00}/\gamma_{11} \neq 1$, with $u(t) = \begin{pmatrix}1 & t\\ 0 & 1\end{pmatrix}$ and $\nu$ the measure component of `productionPinsOf` for the data $\Phi_K$, the principal levels intersected with the kernel of the archimedean projection, the Hecke generators `heckeGen` and the box `adelicBox K`, namely the additive adelic Haar measure conditioned on that box.
--
--   This is the hyperbolic contribution to the truncated trace formula for $\mathrm{GL}_2$ over a number field: the truncated hyperbolic integral grows affinely in the logarithmic truncation height $R$, the linear coefficient being the weighted-orbital-integral term. It is the version for test functions with a unit factorisation outside a finite set $S$ of finite places, and it feeds the assembly of the full truncated kernel in [`AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization.lean

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

theorem AutomorphicForm.exists_tendsto_setIntegral_hyperbolicCell_sub_affine_atTop_of_isUnitFactorization
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
    ∃ a b : ℂ, Filter.Tendsto (fun R : ℝ =>
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
      ((R : ℂ) * a + b)) Filter.atTop (nhds 0) := by sorry
