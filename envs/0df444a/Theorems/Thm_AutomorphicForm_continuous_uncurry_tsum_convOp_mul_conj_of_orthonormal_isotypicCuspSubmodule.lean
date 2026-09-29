-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_uncurry_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
-- name    : AutomorphicForm.continuous_uncurry_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6dc06bb6-0eb7-5ee8-8910-95b6f2709cbe
-- title:
--   Joint continuity and automorphy of the cuspidal kernel
-- statement:
--   Let $K$ be a number field and $0<\alpha<\beta$ reals; let $\Phi_K$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (no hypothesis is imposed on it), and let $c_K,u_K,d_{1K},d_{2K}$ be reals and $T_K$ a finite set of adelic matrices with $0<c_K$, $0<d_{1K}<d_{2K}$, such that the union $\bigcup_{x\in T_K}(\cdot\,x)''$ of right translates of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\ K\ c_K\ u_K\ d_{1K}\ d_{2K}$ (integral finite part, local height $\ge c_K$, $x$-window bounded by $u_K^2$, archimedean determinant norms in $[d_{1K},d_{2K}]$ at every infinite place) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left translation by $\mathrm{GL}_2(K)$ and right multiplication by a central idelic scalar. Let $\nu_{ZK}$ be a Haar measure on $\mathbb{A}_K^\times$ and $\Omega_K$ a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$; let $S_K$ be a finite set of finite places, $\xi_K$ a homomorphism from the full group of ideles (as the top subgroup) to $\mathbb{C}^\times$ which is continuous, unitary ($\|\xi_K(z)\|=1$) and trivial on the image of $K^\times$; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, and $\mathrm{tys}_K$ a family of archimedean types. Write $\alpha_m$ for the homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ via $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume it takes positive values. Fix the carrier data $\mathrm{pins}=\mathrm{productionPinsOf}$ with domain the canonical truncation domain $\mathrm{canonicalTruncationDomain}\ K\ \alpha\ \beta$, level subgroups $M\mapsto\mathrm{principalLevel}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, Hecke generators $v\mapsto\mathrm{heckeGen}\ v$, and the adelic box; its central subgroup is the whole idele class group of units, its measure the adelic Haar measure on $\mathrm{GL}_2$. Let $\iota$ be a type, $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to\mathrm{HeckeEigensystem}\ K\ \mathbb{C}$ be such that for each $i$ the system $\mathrm{cls}\ i$ is a cusp class (level $N$, vanishing Hecke and central data on $S_K$, nonzero isotypic cusp submodule) and $b\,i$ lies in the isotypic cusp submodule of $\mathrm{cls}\ i$ intersected with the archimedean cut submodule $\mathrm{archCutSubmodule}\ K\ \mathrm{tys}_K$; assume the $b\,i$ are orthonormal for the inner product $\int_{\mathrm{canonicalTruncationDomain}} b\,i\cdot\overline{b\,j}$ against the adelic Haar measure; assume each cusp class $\pi$ has finite fibre $\{i\mid \mathrm{cls}\ i=\pi\}$ whose image under $b$ spans the isotypic cusp submodule of $\pi$ cut by the archimedean types; and assume completeness: any $\varphi$ which is a smooth cuspidal automorphic function for these data and $\xi_K$, continuous, right invariant under $\mathrm{pins}.U\ N$, lying in the archimedean cut submodule and orthogonal to every $b\,i$ over the truncation domain, vanishes almost everywhere on the truncation domain. Finally let $f:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, factorizable into a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor, bi-invariant under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, and archimedean bi-finite for $\mathrm{tys}_K$. Then the kernel $(x,y)\mapsto\sum_{i}'\,(\mathrm{convOp}\ K\ f\ (b\,i))(x)\cdot\overline{b\,i(y)}$, where $\mathrm{convOp}\ K\ f\ \varphi(g)=\int \varphi(gx)f(x)\,dx$, is continuous on $\mathrm{GL}_2(\mathbb{A}_K)\times\mathrm{GL}_2(\mathbb{A}_K)$; it is unchanged when either variable is translated on the left by the image of a $\gamma\in\mathrm{GL}_2(K)$; and for every idele unit $a$ it is multiplied by $\xi_K(a)$ when the first variable is multiplied by the central scalar $a$, and by $\xi_K(a)^{-1}$ when the second variable is.
--
--   This is the regularity and equivariance statement for the cuspidal block $K^{\mathrm{cusp}}_f(x,y)=\sum_i (f*b_i)(x)\overline{b_i(y)}$ attached to an adapted orthonormal system of cusp forms: joint continuity, left $\mathrm{GL}_2(K)$-invariance in each variable, and the central character behaviour $\xi_K$ in the first and $\xi_K^{-1}$ in the second. It feeds the pointwise and integrated forms of the spectral expansion used for the axis continuation of the trace identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_uncurry_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.continuous_uncurry_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    (Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
        ∑' i : ι, convOp K f (b i) p.1 * conj (b i p.2)) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑' i : ι, convOp K f (b i) (AutomorphicForm.globalPoints (𝓞 K) K γ * x) * conj (b i y)) =
      (∑' i : ι, convOp K f (b i) x * conj (b i y))) ∧
    (∀ (γ : GL (Fin 2) K) (x y : AdelicGL2 (𝓞 K) K),
      (∑' i : ι, convOp K f (b i) x * conj (b i (AutomorphicForm.globalPoints (𝓞 K) K γ * y))) =
      (∑' i : ι, convOp K f (b i) x * conj (b i y))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑' i : ι, convOp K f (b i) (AutomorphicForm.centralScalar (𝓞 K) K a * x) * conj (b i y)) =
      ((ξK ⟨a, Subgroup.mem_top a⟩ : ℂˣ) : ℂ) *
      (∑' i : ι, convOp K f (b i) x * conj (b i y))) ∧
    (∀ (a : (AdeleRing (𝓞 K) K)ˣ) (x y : AdelicGL2 (𝓞 K) K),
      (∑' i : ι, convOp K f (b i) x * conj (b i (AutomorphicForm.centralScalar (𝓞 K) K a * y))) =
      (((ξK ⟨a, Subgroup.mem_top a⟩)⁻¹ : ℂˣ) : ℂ) *
      (∑' i : ι, convOp K f (b i) x * conj (b i y))) := by sorry
