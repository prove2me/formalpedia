-- Prove2me | Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero
-- name    : AutomorphicForm.isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/7bb8cf8b-a799-5d9d-a006-5b7bf08b6209
-- title:
--   Smoothing an a.e.-cuspidal automorphic function on GL₂
-- statement:
--   Let $K$ be a number field. Fix reals $0<\alpha<\beta$, a set $\Phi_K$ of adelic $\mathrm{GL}_2$-matrices, reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb A_K)$ such that the union of the right translates $(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\ K\,c_K\,u_K\,d_{1K}\,d_{2K}]$, $x\in T_K$, covers $\mathrm{GL}_2(\mathbb A_K)$ modulo global points and the adelic centre; a Haar measure $\nu_{Z_K}$ on $\mathbb A_K^\times$ together with a fundamental domain $\Omega_K$ for the image of $K^\times$; a finite set $S_K$ of finite places; a character $\xi_K$ of the full unit group $\mathbb A_K^\times$ (viewed as $\top$) with values in $\mathbb C^\times$ which is continuous, trivial on the image of $K^\times$ and of absolute value $1$ everywhere; an ideal $N\subseteq\mathcal O_K$ all of whose prime divisors lie in $S_K$; and a family $\mathrm{tys}_K$ of archimedean types, consisting for each infinite place $w$ of finitely many representations of the relevant row-isometry subgroup of $\mathrm{GL}_2(K_w)$. Write $P$ for the production pins attached to the canonical truncation domain of $(\alpha,\beta)$, the level assignment $M\mapsto \mathrm{principalLevel}(M)\cap \ker(\mathrm{glArch})$, the Hecke generators at finite places and the adelic box: thus the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb A_K)$, central subgroup $\top$, and $P.\nu$ the additive adelic Haar measure conditioned on the adelic box. Then for every $u:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying $\mathrm{IsAutomorphicFnAt}$ for $P$ and $\xi_K$ and whose constant term $g\mapsto\int u(\begin{pmatrix}1&q\\0&1\end{pmatrix}g)\,dP.\nu(q)$ vanishes for Haar-almost all $g$, and every continuous, compactly supported $f:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ which factorises as a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor, is bi-invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, and is archimedean bi-finite for $\mathrm{tys}_K$, the right convolution $(\mathrm{convOp}\,K\,f\,u)(g)=\int u(gx)f(x)\,dx$ satisfies: it is a smooth cusp automorphic function at $P$ for $\xi_K$ (automorphic, with identically vanishing constant term, and $K_f$-smooth), it is continuous, it is right invariant under $P.U\,N=\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, and it lies in the archimedean cut submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tys}_K$.
--
--   This is the smoothing step for automorphic forms on $\mathrm{GL}_2$ over a number field: convolution on the right by a $K$-finite test function of level $N$ turns an almost-everywhere cuspidal square-integrable automorphic function into an honest continuous smooth cusp form of level $N$ and of the prescribed archimedean types. It feeds the construction of orthonormal systems in isotypic cusp spaces, being cited in the derivation that such a convolution vanishes almost everywhere on the canonical truncation domain once all its inner products against the system vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero.lean

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

theorem AutomorphicForm.isSmoothCuspAutomorphicFnAt_convOp_and_continuous_and_mem_archCutSubmodule_of_ae_constantTerm_eq_zero
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
    ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u →
      (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 u g = 0) →
    ∀
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (convOp K f u) ∧
    Continuous (convOp K f u) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, convOp K f u (g * k) = convOp K f u g) ∧
    convOp K f u ∈ archCutSubmodule K tysK := by sorry
