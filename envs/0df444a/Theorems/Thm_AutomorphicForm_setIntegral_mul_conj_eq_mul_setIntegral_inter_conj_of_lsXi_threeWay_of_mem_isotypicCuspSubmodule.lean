-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule
-- name    : AutomorphicForm.setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/b4a01f5f-cc47-5704-a0de-a479085a70c4
-- title:
--   Cuspidal component of the automorphised indicator
-- statement:
--   Let $K$ be a number field, and let $0<\alpha<\beta$ be reals; write $\Phi_0=$ `canonicalTruncationDomain K α β` and let $\mu$ be the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $GL_2$ of the adeles. The following data are assumed: a set $\Phi_K$ of adelic matrices; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ and $0<d_{1K}<d_{2K}$ and a finite set $T_K$ of adelic matrices such that the union of the right translates $(\cdot\,x)''\,$`centreCutSiegelSet K cK uK d₁K d₂K` over $x\in T_K$ covers $GL_2(\mathbb{A}_K)$ modulo left global points and central scalars; a Haar measure $\nu_{Z}$ on $\mathbb{A}_K^\times$ together with a fundamental domain $\Omega_K$ for the image of $K^\times$; a finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full unit group (as the top subgroup) to $\mathbb{C}^\times$ that is continuous, unitary, and trivial on the image of $K^\times$; an ideal $N$ all of whose prime divisors lie in $S_K$; and a family `tysK` of archimedean types. Throughout, the carrier data are `productionPinsOf K Φ₀ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, so that the group measure is $\mu$, the domain is $\Phi_0$, the central subgroup is $\top$, and the unipotent-integration measure is the additive adelic Haar measure conditioned on `adelicBox K`. The assertion is: for every index type $\iota$, every family $b:\iota\to (GL_2(\mathbb{A}_K)\to\mathbb{C})$ and every family $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` such that, for each $i$, $\mathrm{cls}\,i$ lies in `cuspClasses` for $\xi_K$, $N$, $S_K$ (its level is $N$, its Hecke and central parameters vanish on $S_K$, and its isotypic cusp submodule is non-zero) and $b\,i$ lies in the isotypic cusp submodule attached to $\mathrm{cls}\,i$ intersected with the archimedean type submodule `archCutSubmodule K tysK`; and for every compact $C$, measurable $B\subseteq C$, and functions $u_c,u_r,u_e$ with: $u_c$ automorphic for these pins and $\xi_K$ with $\mu$-a.e. vanishing constant term along the unipotent $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$; $u_r$ automorphic and approximable in the $L^2$-norm over $\Phi_0$, to within any $\varepsilon>0$, by automorphic elements of the residual span spanned by the functions $g\mapsto\chi(\det g)$ with $\chi^2=\xi_K$ on the central subgroup; $u_e$ automorphic and $\Phi_0$-orthogonal to every automorphic $h$ whose constant term vanishes a.e. or which lies in that residual span; and with $u_c+u_r+u_e$ equal, a.e. on $\Phi_0$ for $\mu$ restricted to $\Phi_0$, to the automorphisation $g\mapsto\sum_{q\in GL_2(K)/Z(GL_2(K))}\int \xi_K(w)^{-1}\mathbf 1_{\Phi_0\cap B}\bigl(w\cdot(q\,g)\bigr)\,d\nu_{Z}(w)$ (central scalars and global points taken via the respective homomorphisms, the coset representative via `Quotient.out`), one has for every $i$ $$\int_{\Phi_0}u_c(g)\,\overline{b\,i\,(g)}\,d\mu=\nu_{Z}\bigl(\Omega_K\cap\{z:\ \text{ideleNorm}_K(\det(z\cdot 1))\in[\alpha,\beta]\}\bigr)\cdot\int_{\Phi_0\cap B}\overline{b\,i\,(g)}\,d\mu,$$ the measure of the slab being taken as a real number.
--
--   This is the computation of the cuspidal Fourier coefficient of the automorphised indicator of a measurable set $B$: pairing the cuspidal part of the three-way (cuspidal/residual/orthogonal) decomposition against an isotypic cusp form returns the integral of that form over $\Phi_0\cap B$, scaled by the volume of the central slab $\Omega_K\cap\{\|z\|\in[\alpha,\beta]\}$. It feeds the cuspidal rectangle estimate [`AutomorphicForm.setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule`](thm.html#AutomorphicForm.setIntegral_convOp_cuspProjection_eq_mul_setIntegral_prod_tsum_convOp_mul_conj_of_orthonormal_isotypicCuspSubmodule), and relies on the unfolding of the automorphisation against an automorphic function together with the vanishing of the pairing of cuspidal and residual contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule.lean

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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_mul_conj_eq_mul_setIntegral_inter_conj_of_lsXi_threeWay_of_mem_isotypicCuspSubmodule
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
    letI := adeleBorel (𝓞 K) K
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK),
    ∀ (C : Set (AdelicGL2 (𝓞 K) K)) (_hC : IsCompact C)
      (B : Set (AdelicGL2 (𝓞 K) K)) (_hB : B ⊆ C) (_hBm : MeasurableSet B)
      (uc ur ue : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc) (_huc0 : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc g = 0))
      (_hur : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur)
      (_hurc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum : (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator (B.indicator fun _ => (1 : ℂ))
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc + ur + ue),
    ∀ i : ι, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, uc g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
      ∫ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ B, conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
