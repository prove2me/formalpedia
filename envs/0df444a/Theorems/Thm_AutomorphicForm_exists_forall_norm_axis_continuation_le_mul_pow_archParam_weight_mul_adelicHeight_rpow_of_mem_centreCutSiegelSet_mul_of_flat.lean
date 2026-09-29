-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat
-- name    : AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/bd07a7a0-dfb6-5d0f-9083-45301c5d5951
-- title:
--   Uniform moderate growth of GL₂ Eisenstein series on centre-cut Siegel sets
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places of $K$, and $\xi_K$ a homomorphism from the full group of ideles $(\mathbb{A}_K)^\times$ (presented as the top subgroup) to $\mathbb{C}^\times$ which is continuous and trivial on the principal ideles, i.e. on the image of $K^\times$; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be an archimedean type family (for each infinite place a finite list of finite-dimensional representations of the local row-isometry group), and let $w \in \mathbb{R}$ satisfy $|\xi_K(z)| = \|z\|^{w}$, where $\|\cdot\|$ is the idele norm given by the module character of the adele ring. Let $c,u,d_1,d_2$ be reals with $c>0$ and let $\Omega \subseteq GL_2(\mathbb{A}_K)$ be compact. Write $\alpha$ for the idele norm viewed as a character into $\mathbb{R}^\times$. The assertion is the existence of $C>0$, $A \in \mathbb{N}$ and $B \in \mathbb{R}$, depending only on these data, such that the following bound holds for all further data: a proof that $\alpha$ takes positive values; continuous unitary characters $\mu,\nu$ of $(\mathbb{A}_K)^\times$ trivial on $K^\times$ with $\mu(z)\nu(z)\|z\|^{w} = \xi_K(z)$; archimedean parameters $\tau^\mu,\tau^\nu : \mathrm{InfinitePlace}(K) \to \mathbb{R}$ describing the local components of $\mu,\nu$ on positive real units as $\|\cdot\|^{i\tau_v}$, and weights $m^\mu,m^\nu : \mathrm{InfinitePlace}(K) \to \mathbb{Z}$ describing them on norm-one units as $x \mapsto x^{m_v}$; a family $\psi_s$ on $GL_2(\mathbb{A}_K)$ such that each $\psi_s$ is a section of the induced model for the pair $(\mu\alpha^{s+1/2}, \nu\alpha^{-(s+1/2)})$, i.e. $\psi_s(bg)$ equals the product of those two characters evaluated at the two diagonal entries of the Borel element $b$ times $\psi_s(g)$, which is archimedean $K$-finite, smooth for the finite adelic subgroup, jointly continuous in $(s,g)$ and holomorphic in $s$, with right translates under each archimedean row-isometry subgroup lying in a fixed finite-dimensional space, flat in the sense that $\psi_s(k) = \psi_0(k)$ for $k$ in the adelic maximal compact subgroup, right invariant under the principal level of $N$ intersected with the finite adelic subgroup, of type $\mathrm{tys}_K$, and normalised by $\int_{\mathbf{K}} |\psi_0|^2 \le 1$; and a set $O_\psi$ together with functions $E_\psi, N_\psi$ such that $O_\psi$ is open, preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$, $E_\psi$ and $N_\psi$ are analytic in $s$ on a neighbourhood of $O_\psi$ and continuous on $O_\psi \times GL_2(\mathbb{A}_K)$, and for $\mathrm{Re}\,s > 1/2$ one has $E_\psi(s,g) = \psi_s(g) + \sum_{\xi \in K} \psi_s(w\,u(\xi)\,g)$ with $w$ the Weyl element and $u(\xi)$ the upper unipotent, while $N_\psi(s,g)$ is the Weyl intertwining integral of $\psi_s$ against adelic additive Haar measure. Then, for every $t \in \mathbb{R}$, every $x$ in the centre-cut Siegel set $\mathfrak{S}(c,u,d_1,d_2)$ — elements whose finite part is integral, whose local height at each infinite place is at least $c$, whose squared window parameter is at most $u^2$, and whose archimedean determinant norms lie in $[d_1,d_2]$ — and every $\omega \in \Omega$, $$\|E_\psi(it, x\omega)\| \le C\Bigl(1 + \sum_{v \mid \infty}\bigl(|t+\tau^\mu_v| + |t-\tau^\nu_v| + |m^\mu_v| + |m^\nu_v|\bigr)\Bigr)^{A} H(x\omega)^{B},$$ where $H$ is the adelic height.
--
--   This is the moderate-growth estimate for the analytic continuation to the unitary axis of $GL_2$ Eisenstein series, stated uniformly over all inducing data of the given level, central character and archimedean types, with the dependence on the spectral parameter polynomial and the dependence on the point a fixed power of the adelic height. It is the form of the bound on a centre-cut Siegel set translated by a compact set; the corresponding bound on arbitrary compact subsets of $GL_2(\mathbb{A}_K)$ is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat.lean

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
open AutomorphicForm.WindowedSiegel
open AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_of_mem_centreCutSiegelSet_mul_of_flat
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Ω : Set (AdelicGL2 (𝓞 K) K)) (hΩ : IsCompact Ω)
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
      (t : ℝ), ∀ x ∈ centreCutSiegelSet K c u d₁ d₂, ∀ ω ∈ Ω,
      ‖Eψ ((t : ℂ) * Complex.I) (x * ω)‖ ≤
        C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
          NumberField.AdelicHeight.adelicHeight K (x * ω) ^ B := by sorry
