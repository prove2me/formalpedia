-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- name    : AutomorphicForm.exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/952f0dca-086e-5dc9-b2e5-4315f50a778c
-- title:
--   Uniform rapid decay of non-constant part of GL₂ Eisenstein series
-- statement:
--   Fix a number field $K$, a finite set $S_K$ of finite places of $K$, and a continuous character $\xi_K$ of the full group of ideles $(\mathbb{A}_K)^\times$ (presented as a character of the top subgroup) that is trivial on the principal ideles and satisfies $|\xi_K(z)|=\|z\|^{w}$ for a fixed real $w$, where $\|z\|$ is the module of $z$ (the value of the distributive Haar character of $\mathbb{A}_K$); fix an ideal $N$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, a family $\mathrm{tys}_K$ of archimedean $K$-types (for each infinite place a finite list of representations of the row-isometry subgroup of the completion), a compact set $\Omega\subseteq \mathrm{GL}_2(\mathbb{A}_K)$, a real $c'>0$ and a natural number $N'$. Write $\alpha$ for the real-valued module character of the ideles. The assertion is the existence of $C>0$ and $A\in\mathbb{N}$, depending only on these data, such that the following holds for all further data: a pair $\mu,\nu$ of continuous unitary idele class characters (unit absolute values, trivial on $K^\times$) with $\mu\nu\|\cdot\|^{w}=\xi_K$; archimedean spectral parameters $\tau^\mu,\tau^\nu:\,$ infinite places $\to\mathbb{R}$ such that at each infinite place $v$ the local component of $\mu$ (resp. $\nu$) on units mapping to positive reals under the embedding of $K_v$ equals $\|\cdot\|^{\,i\tau^\mu_v}$ (resp. $\|\cdot\|^{\,i\tau^\nu_v}$); weights $m^\mu,m^\nu:\,$ infinite places $\to\mathbb{Z}$ such that on norm-one units the local component of $\mu$ (resp. $\nu$) is the $m^\mu_v$-th (resp. $m^\nu_v$-th) power of the embedding; a family $s\mapsto\psi_s$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ with $\psi_s(bg)=\mu\alpha^{s+1/2}(a)\,\nu\alpha^{-(s+1/2)}(d)\,\psi_s(g)$ for $b$ upper triangular with diagonal entries $a,d$, archimedean $K$-finite, $K_f$-smooth, jointly continuous in $(s,g)$, holomorphic in $s$ for each $g$, with right translates under each archimedean row-isometry subgroup lying in one fixed finite-dimensional space of functions independent of $s$ and $g$, flat in the sense that $\psi_s=\psi_0$ on the adelic maximal compact subgroup, invariant under right translation by the intersection of the principal level subgroup of level $N$ with the finite-adelic subgroup, lying in the submodule cut out by $\mathrm{tys}_K$, and normalised by $\int_{\mathbf{K}}|\psi_0|^2\le 1$ against Haar measure on the maximal compact; and finally an open preconnected set $O_\psi\subseteq\mathbb{C}$ containing both the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$, together with functions $E_\psi,N_\psi$ on $O_\psi\times\mathrm{GL}_2(\mathbb{A}_K)$, analytic in $s$ for each $g$ and continuous on $O_\psi\times\mathrm{GL}_2(\mathbb{A}_K)$, such that for $\mathrm{Re}\,s>1/2$ one has $E_\psi(s,g)=\psi_s(g)+\sum_{\xi\in K}\psi_s(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element and $n(\xi)$ the unipotent matrix, and $N_\psi(s,g)=\int_{\mathbb{A}_K}\psi_s(w^{-1}n(x)g)\,dx$ against adelic additive Haar measure. Under these hypotheses, for every $t\in\mathbb{R}$, every upper-triangular $b\in\mathrm{GL}_2(\mathbb{A}_K)$ with diagonal entries $a,d$, and every $\omega\in\Omega$ with $\alpha(a)/\alpha(d)\ge c'$, the difference between $E_\psi(it,b\omega)$ and its constant term $\int E_\psi(it,n(u)b\omega)$, taken against the additive adelic Haar measure conditioned on the adelic box, has absolute value at most $$C\Bigl(1+\sum_{v\mid\infty}\bigl(|t+\tau^\mu_v|+|t-\tau^\nu_v|+|m^\mu_v|+|m^\nu_v|\bigr)\Bigr)^{A}\bigl(\alpha(a)/\alpha(d)\bigr)^{-N'}.$$
--
--   This is the rapid decay, on Siegel sets written in Borel coordinates $b\omega$ with torus height bounded below, of the non-constant part of the Eisenstein series attached to a flat holomorphic family of induced sections on $\mathrm{GL}_2$ over a number field, in a form uniform in the inducing unitary characters of fixed level and archimedean types and polynomial in the archimedean spectral parameters and weights. It is used in the subsequent treatment of the spectral decomposition and of convolution integrals against Eisenstein contributions, where the constants $C$ and $A$ must not depend on the character pair $(\mu,\nu)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat.lean

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

theorem AutomorphicForm.exists_forall_norm_axis_continuation_sub_constantTerm_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat
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
    (Ω : Set (AdelicGL2 (𝓞 K) K)) (hΩ : IsCompact Ω) (c' : ℝ) (hc' : 0 < c') (N' : ℕ)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
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
      (t : ℝ) (b : ↥(adelicBorel (𝓞 K) K)) (ω : AdelicGL2 (𝓞 K) K),
      ω ∈ Ω → c' ≤ (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) →
      ‖Eψ ((t : ℂ) * Complex.I) ((b : AdelicGL2 (𝓞 K) K) * ω) -
          AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
          (fun u => AutomorphicForm.unipotentGL2 u) (Eψ ((t : ℂ) * Complex.I)) ((b : AdelicGL2 (𝓞 K) K) * ω)‖ ≤
        C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
          (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N' : ℝ)) := by sorry
