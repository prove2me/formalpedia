-- Prove2me | Theorems.Thm_AutomorphicForm_integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul
-- name    : AutomorphicForm.integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c21e1f86-aec6-564e-b280-76602e04f442
-- title:
--   Centre unfolding of hyperbolic orbital integrals over K
-- statement:
--   Let $K$ be a number field, let $\nu_{ZK}$ be a Haar measure on the idele group $(\mathbb{A}_K)^\times$, and let $\xi$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated function $z \mapsto \xi(z)$ into $\mathbb{C}$ is continuous. Let $H_K \le \mathrm{GL}_2(\mathbb{A}_K)$ be a closed subgroup consisting exactly of those invertible matrices whose $(1,0)$ and $(0,1)$ entries vanish, equipped with a right-invariant Haar measure $\mu_{H_K}$, and suppose that for some $c_{H_K} > 0$ one has $\int_{H_K} g\,d\mu_{H_K} = c_{H_K}\int\int g(z\cdot 1_2 \cdot \mathrm{diag}(a,1))\,d(\nu_{ZK}\otimes\nu_{ZK})(z,a)$ for every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, where $z \cdot 1_2$ denotes the central scalar matrix; fix also $c_{\tau K} > 0$. The conclusion is asserted for every $\gamma \in \mathrm{GL}_2(K)$ with vanishing off-diagonal entries and $\gamma_{00}/\gamma_{11} \ne 1$, every Haar measure $\tau$ on the centraliser of the adelic image $\gamma_{\mathbb{A}}$ of $\gamma$ (Borel $\sigma$-algebra) satisfying $\int_{\mathrm{Cent}} g\,d\tau = c_{\tau K}\int\int g(\mathrm{diag}(a,d))\,d(\nu_{ZK}\otimes\nu_{ZK})(a,d)$ for all $g$, and every continuous $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ of compact support. It has two parts. First, let $I : (\mathbb{A}_K)^\times \to \mathbb{C}$ be such that for each idele $z$ the value $I(z)$ is an orbital integral of $g \mapsto f(z\cdot 1_2 \cdot g)$ at $\gamma_{\mathbb{A}}$ relative to $\tau$ and the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, i.e. there is a non-negative measurable compactly supported $w$ with $\int w(tx)\,d\tau(t) = 1$ whenever $f(z\cdot 1_2 \cdot x^{-1}\gamma_{\mathbb{A}}x) \ne 0$ and $I(z) = \int f(z\cdot 1_2 \cdot x^{-1}\gamma_{\mathbb{A}}x)\,w(x)\,dx$; assume that $q \mapsto \int \xi(z) f(q^{-1}\gamma_{\mathbb{A}} (z\cdot 1_2) q)\,d\nu_{ZK}(z)$, evaluated at chosen representatives $q$, is integrable on the orbit quotient by $H_K$ for the quotient measure built from the adelic Haar measure and $\mu_{H_K}$. Then $z \mapsto \xi(z)I(z)$ is $\nu_{ZK}$-integrable and the quotient integral of that function equals $(c_{\tau K}/c_{H_K})\int \xi(z)I(z)\,d\nu_{ZK}$. Second, the same assertion holds with the real weight $x \mapsto -\log H(x) - \log H(w\,x)$ inserted, where $H$ is the adelic height and $w$ is the adelic image of the antidiagonal Weyl element: if $J(z)$ is a corresponding weighted orbital integral $\int f(z\cdot 1_2 \cdot x^{-1}\gamma_{\mathbb{A}}x)\,\mathrm{wt}(x)\,s(x)\,dx$ for a section function $s$, and the weighted class integrand is integrable on the quotient, then $z \mapsto \xi(z)J(z)$ is integrable and the weighted quotient integral equals $(c_{\tau K}/c_{H_K})\int \xi(z)J(z)\,d\nu_{ZK}$.
--
--   This is the centre-unfolding step for a regular hyperbolic (split, non-central) conjugacy class over $K$: the integral of the class contribution over $H_K \backslash \mathrm{GL}_2(\mathbb{A}_K)$, with the central variable integrated against $\xi$, is identified with a multiple of the corresponding ordinary and weighted orbital integrals, the constant being the ratio of the two unfolding constants. It feeds the computation of the hyperbolic part of the adelic kernel over the canonical truncation domain, where the hyperbolic terms are matched against sums of (weighted) orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul.lean

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

theorem AutomorphicForm.integral_haarQuotient_orbital_eq_const_mul_integral_of_isOrbitalIntegralOn_centralScalar_mul
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))

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

    (∀ (I : (AdeleRing (𝓞 K) K)ˣ → ℂ),
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (I z)) →
      Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) →
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * I z) νZK ∧
      ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
            (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) =
        ((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * I z ∂νZK) ∧

    (∀ (J : (AdeleRing (𝓞 K) K)ˣ → ℂ),
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (J z)) →
      Integrable (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK))
        (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) →
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * J z) νZK ∧
      ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
            ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) * (∫ z, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K)))) ∂νZK)
          ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) =
        ((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * J z ∂νZK) := by sorry
