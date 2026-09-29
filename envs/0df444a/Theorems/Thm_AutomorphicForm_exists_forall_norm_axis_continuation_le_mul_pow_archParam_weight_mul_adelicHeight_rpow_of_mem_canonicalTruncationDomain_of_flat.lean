-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
-- name    : AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/91dcddbf-763e-5c27-9bfc-c4a97f1ff810
-- title:
--   Uniform moderate growth of flat Eisenstein series on the truncation domain
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places of $K$, and $\xi_K$ a homomorphism from the full group of ideles (viewed as the top subgroup) to $\mathbb C^\times$ which is continuous, trivial on the image of $K^\times$, and of modulus $\|\xi_K(z)\| = \mathrm{ideleNorm}(z)^w$ for a real $w$, where $\mathrm{ideleNorm}$ is the real value of the module character `distribHaarChar` of the adele ring; let $N$ be an ideal of $\mathcal O_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be an `ArchTypeFamily` (for each infinite place a finite list of representations of the row-isometry group of the completion), and let $0<\alpha<\beta$ be reals. Write $\alpha_m$ for the idele character $z \mapsto \mathrm{ideleNorm}(z)$ regarded as a homomorphism into $\mathbb R^\times$. Then there exist $C>0$, $A \in \mathbb N$ and $B \in \mathbb R$ such that the following holds, given: positivity of $\alpha_m$; continuous unitary idele characters $\mu,\nu$ (each of absolute value $1$ everywhere and trivial on $K^\times$) with $\mu(z)\nu(z)\,\mathrm{ideleNorm}(z)^w = \xi_K(z)$; real archimedean parameters $\tau^\mu_v,\tau^\nu_v$ such that at each infinite place $v$ the local component of $\mu$ (resp. $\nu$), restricted to units of $K_v$ whose embedding is a positive real, equals $\mathrm{ideleNorm}^{\,\tau_v i}$; integers $m^\mu_v,m^\nu_v$ such that on units of norm $1$ the local component of $\mu$ (resp. $\nu$) is the $m_v$-th power of the embedding; a family $\psi : \mathbb C \to \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ such that each $\psi_s$ is a section induced from the pair of Borel characters $\mu\,\alpha_m^{s+1/2}$ and $\nu\,\alpha_m^{-(s+1/2)}$ (i.e. $\psi_s(bg)$ equals the product of these characters evaluated at the two diagonal entries of $b$, times $\psi_s(g)$), is archimedean $K$-finite place by place, is $K_f$-smooth (its stabiliser in the finite adelic subgroup is open), jointly continuous in $(s,g)$, holomorphic in $s$, uniformly $K$-finite at each infinite place through a single finite-dimensional space $W$ of functions on the row-isometry subgroup, flat in the sense that $\psi_s(k)=\psi_0(k)$ for $k$ in the adelic maximal compact, right invariant under $\mathrm{principalLevel}\,N$ intersected with the finite adelic subgroup, of the prescribed archimedean types, and normalised by $\int_{\mathbf K} \|\psi_0\|^2 \le 1$; a set $O_\psi \subseteq \mathbb C$ and functions $E_\psi, N_\psi$ subject to the package: $O_\psi$ open, preconnected, containing both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$, with $E_\psi$ and $N_\psi$ analytic in $s$ on $O_\psi$ for each $g$ and jointly continuous on $O_\psi \times \mathrm{GL}_2(\mathbb A_K)$, and, for $\mathrm{Re}\,s>1/2$, $E_\psi(s,g) = \psi_s(g) + \sum_{\xi \in K} \psi_s(\mathrm{w}\,u(\xi)\,g)$ with $\mathrm{w}$ the adelic Weyl element and $u(\xi)$ the unipotent matrix, while $N_\psi(s,g)$ is the Weyl intertwining integral of $\psi_s$ against the additive adelic Haar measure; and a real $t$. The conclusion is that for every $x$ in $\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$ (the domain component of the chosen truncation datum for $\alpha,\beta$), $$\|E_\psi(it,x)\| \le C\Bigl(1+\sum_{v \mid \infty}\bigl(|t+\tau^\mu_v|+|t-\tau^\nu_v|+|m^\mu_v|+|m^\nu_v|\bigr)\Bigr)^{A}\,\mathrm{adelicHeight}_K(x)^{B},$$ where the adelic height is the product of the archimedean height of the infinite part and the finite height of the finite part.
--
--   This is the moderate-growth estimate for unitary $\mathrm{GL}_2$ Eisenstein series restricted to the canonical truncation domain, in the form where the constant is polynomial in the archimedean spectral parameters and weights and is uniform over all inducing data of the given level, central character and archimedean types. It supports the subsequent integrability and orthogonality computations over the truncation domain, where such a bound is needed to interchange integration with spectral sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain_of_flat
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ) (B : ℝ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ), ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      ‖Eψ ((t : ℂ) * Complex.I) x‖ ≤
        C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
          NumberField.AdelicHeight.adelicHeight K x ^ B := by sorry
