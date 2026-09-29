-- Prove2me | Theorems.Thm_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
-- name    : AutomorphicForm.const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/fc2bd695-7fa5-568c-b8cb-6ec1066b4568
-- title:
--   Unfolding a central-translate orbital integral over H_Kbackslash GL₂(mathbb A_K)
-- statement:
--   Let $K$ be a number field and $\nu_{Z}$ a Haar measure on the idele group $(\mathbb A_K)^\times$ (equipped with a Borel measurable structure). Let $H_K\le GL_2(\mathbb A_K)$ be a closed subgroup consisting exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish, carrying a right-invariant Haar measure $\mu_{H_K}$, and suppose that for a constant $c_{H_K}>0$ every function $g:GL_2(\mathbb A_K)\to\mathbb C$ satisfies $\int_{H_K} g\,d\mu_{H_K}=c_{H_K}\int g(\mathrm{diag}(z,z)\cdot\mathrm{diag}(a,1))\,d(\nu_Z\times\nu_Z)(z,a)$, where the central scalar is [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) and $\mathrm{diag}$ is `diagUnits2`; let $c_{\tau K}>0$. Then for every $\gamma\in GL_2(K)$ with vanishing $(1,0)$ and $(0,1)$ entries and $\gamma_{00}/\gamma_{11}\ne 1$, every Haar measure $\tau$ on the centraliser of the adelic image $\gamma_{\mathbb A}$ of $\gamma$ (Borel structure [`AutomorphicForm.centralizerBorel`](def/AutomorphicForm_TwistedOrbital.html#L62)) satisfying the analogous unfolding $\int g\,d\tau=c_{\tau K}\int g(\mathrm{diag}(a,d))\,d(\nu_Z\times\nu_Z)(a,d)$ for all $g$, and every continuous compactly supported $f:GL_2(\mathbb A_K)\to\mathbb C$, two assertions hold. First, for every idele $z$ and every $I\in\mathbb C$: if $I$ is a value of the orbital integral of $g\mapsto f(\mathrm{diag}(z,z)g)$ at $\gamma_{\mathbb A}$ relative to $\tau$ and the Haar measure `adelicGLHaar` on $GL_2(\mathbb A_K)$ — that is, there is a non-negative measurable compactly supported $w$ with $\int_{Z(\gamma_{\mathbb A})} w(tx)\,d\tau=1$ whenever $f(\mathrm{diag}(z,z)x^{-1}\gamma_{\mathbb A}x)\ne 0$, and $I=\int f(\mathrm{diag}(z,z)x^{-1}\gamma_{\mathbb A}x)\,w(x)\,dx$ — then $$(c_{\tau K}/c_{H_K})\,I=\int_{q} f\bigl(q^{-1}\gamma_{\mathbb A}\,\mathrm{diag}(z,z)\,q\bigr),$$ the integral being over the quotient of $GL_2(\mathbb A_K)$ by the orbit relation of $H_K$ against the quotient measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28) built from `adelicGLHaar`, $H_K$ and $\mu_{H_K}$, with $q$ standing for a chosen representative `q.out` of the orbit. Secondly, the same identity with $I$ replaced by any value $J$ of the weighted orbital integral with weight $x\mapsto -\log H(x)-\log H(w_{\mathbb A}x)$, where $H$ is [`NumberField.AdelicHeight.adelicHeight`](def/NumberField_AdelicHeight.html#L158) and $w_{\mathbb A}$ is the adelic Weyl element, the same weight evaluated at the representative being inserted into the quotient integrand.
--
--   This is the unfolding step, in Weil's quotient-integral form, identifying the orbital and weighted orbital integrals of a central translate of $f$ at a regular diagonal element of $GL_2(K)$ with integrals over $H_K\backslash GL_2(\mathbb A_K)$, under explicit normalisations of the Haar measures on $H_K$ and on the centraliser by the torus $(\mathbb A_K^\times)^2$. It feeds the companion statement [`AutomorphicForm.integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul`](thm.html#AutomorphicForm.integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul), used in the comparison of trace-formula terms for the untwisted group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal.lean

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
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]

    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]
    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK) :
    ∀ (γ : GL (Fin 2) K), (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 → (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1 →
    ∀ (τ : @Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)))
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)) τ →
      (∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
            g (s : AdelicGL2 (𝓞 K) K) ∂τ =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) →
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →

    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) I →
      ((cτK / cHK : ℝ) : ℂ) * I =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) ∧

    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) J →
      ((cτK / cHK : ℝ) : ℂ) * J =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) := by sorry
