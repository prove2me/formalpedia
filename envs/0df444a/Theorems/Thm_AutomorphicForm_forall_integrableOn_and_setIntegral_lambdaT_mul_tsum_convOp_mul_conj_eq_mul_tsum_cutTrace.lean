-- Prove2me | Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
-- name    : AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/fc19ff1c-313b-52b6-b781-aea782a608b5
-- title:
--   Cuspidal block of the truncated GL₂ spectral side
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$, let $\Phi_K$ be a set of elements of $GL_2(\mathbb{A}_K)$, and let $c_K,u_K,d_{1K},d_{2K}$ be reals with $c_K>0$ and $0<d_{1K}<d_{2K}$, together with a finite set $T_K\subseteq GL_2(\mathbb{A}_K)$ whose union of right translates $\bigcup_{x\in T_K}(\cdot\,x)''$ of the centre-cut Siegel set with parameters $c_K,u_K,d_{1K},d_{2K}$ covers $GL_2(\mathbb{A}_K)$ modulo $GL_2(K)$ on the left and the central ideles on the right. Fix a Haar measure $\nu_{Z_K}$ on $\mathbb{A}_K^\times$ with a fundamental domain $\Omega_K$ for the image of $K^\times$, a finite set $S_K$ of finite places, a continuous homomorphism $\xi_K$ from the full group of ideles to $\mathbb{C}^\times$ trivial on principal ideles, an ideal $N$ all of whose prime divisors lie in $S_K$, and a family $\mathrm{tys}_K$ of archimedean types (finitely many representations of the row-isometry subgroup at each infinite place). Let $b:\iota\to(GL_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$ satisfy: each $\mathrm{cls}\,i$ lies in the set of cuspidal classes for $(\xi_K,N,S_K)$ at the production pins with domain the canonical truncation domain $\Phi_0=\Phi_0(K,\alpha,\beta)$, level subgroups $M\mapsto$ principal level $M$ intersected with the finite adelic subgroup, Hecke generators $\mathrm{heckeGen}$ and box the adelic box, and $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ cut by the archimedean types; the $b\,i$ are orthonormal for the Haar measure on $\Phi_0$; for each cuspidal class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $b\,i$ over it span the corresponding cut isotypic submodule; and the system is complete, in the sense that a continuous function $\varphi$ which is smooth cuspidal automorphic at these pins, invariant under right translation by the level subgroup at $N$, lies in the archimedean cut submodule and is orthogonal to every $b\,i$ on $\Phi_0$, vanishes almost everywhere on $\Phi_0$. Put $V=\nu_{Z_K}\bigl(\Omega_K\cap\{z\mid \|\det(z\cdot 1)\|_{\mathbb{A}}\in[\alpha,\beta]\}\bigr)$, viewed in $\mathbb{C}$. The assertion is that for every continuous compactly supported $f$ on $GL_2(\mathbb{A}_K)$ which factorises as a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor, is bi-invariant under the principal level $N$ intersected with the finite adelic subgroup, and is archimedean bi-finite for $\mathrm{tys}_K$, and for every real $R$, the function obtained by applying the truncation operator $\lambda^T$ — subtraction of the indicator of $\{\mathrm{adelicHeight}>e^{R}\}$ times the constant term along the unipotents $t\mapsto u(t)$ against the adelic additive Haar measure conditioned to the adelic box — to the second variable of the cuspidal kernel $y'\mapsto V\sum_{i\in\iota}(\mathrm{convOp}\,f\,(b\,i))(x)\,\overline{b\,i(y')}$ and evaluating on the diagonal at $x$, is integrable on $\Phi_0$, and its integral equals $V$ times the sum over the cuspidal classes $\pi$ for $(\xi_K,N,S_K)$ at the pins with domain the above union of Siegel translates of $\mathrm{cutTrace}$ at $\pi$, that is the trace of $u\mapsto u*f$ on the isotypic cuspidal submodule of $\pi$ cut by $\mathrm{tys}_K$.
--
--   This is the cuspidal contribution to the spectral side of the Arthur–Selberg trace formula for $GL_2$ over a number field, after folding the centre: truncation leaves the cuspidal kernel unchanged, and its diagonal integral over a fundamental domain in the determinant band $[\alpha,\beta]$ equals the volume of the central band times the sum of the traces of right convolution by $f$ on the cut isotypic pieces. It is used in the assembly of the full spectral expansion, where the cuspidal block is separated from the continuous and residual contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace
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
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0) :
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
      ∀ R : ℝ,
        IntegrableOn (fun x =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
        ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc := by sorry
