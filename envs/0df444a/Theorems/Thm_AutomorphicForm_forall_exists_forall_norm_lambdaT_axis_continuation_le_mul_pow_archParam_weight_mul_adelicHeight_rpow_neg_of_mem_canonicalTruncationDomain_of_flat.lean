-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat
-- name    : AutomorphicForm.forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0a34f932-38ad-58e5-957d-402a86d45a85
-- title:
--   Uniform rapid decay of truncated unitary Eisenstein series
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places, $\xi_K$ a continuous character of the full idele group $(\mathbb{A}_K^\times)$ (presented as a character of the top subgroup) which is trivial on the image of $K^\times$ and satisfies $|\xi_K(z)| = \|z\|^w$ for a fixed real $w$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, $\mathrm{tys}_K$ a family assigning to each infinite place finitely many archimedean types, $0 < \alpha < \beta$ real, and $\Phi_K$ a set in $\mathrm{GL}_2(\mathbb{A}_K)$. Write $\alpha_m$ for the idele-norm homomorphism into $\mathbb{R}^\times$. Then for every $N' \in \mathbb{N}$ there are $C > 0$ and $A \in \mathbb{N}$ such that the following holds for all further data: a pair $\mu,\nu$ of continuous unitary characters of $(\mathbb{A}_K^\times)$ trivial on $K^\times$ with $\mu(z)\nu(z)\|z\|^w = \xi_K(z)$; real parameters $\tau_\mu(v), \tau_\nu(v)$ such that at each infinite place the local component of $\mu$ (resp. $\nu$) on positive real units is $\|\cdot\|^{i\tau_\mu(v)}$ (resp. $\|\cdot\|^{i\tau_\nu(v)}$); integers $m_\mu(v), m_\nu(v)$ giving the restriction of the same local characters to norm-one elements as $x \mapsto x^{m_\mu(v)}$ (resp. $x^{m_\nu(v)}$); a family $\psi_s$ of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ which for each $s$ transforms under the adelic Borel by the characters $\mu\,\alpha_m^{s+1/2}$ and $\nu\,\alpha_m^{-(s+1/2)}$ on the two diagonal entries, is archimedean-$K$-finite at each infinite place and with right translates at each place lying in one fixed finite-dimensional space, is $K_f$-smooth, jointly continuous in $(s,g)$, holomorphic in $s$, flat in the sense that $\psi_s(k) = \psi_0(k)$ for $k$ in the adelic maximal compact, right invariant under $\mathrm{principalLevel}(N)$ intersected with the finite adelic subgroup, lies for each $s$ in the submodule cut out by the prescribed archimedean types, and satisfies $\int_{\mathbf{K}} |\psi_0(k)|^2\,dk \le 1$ for the Haar measure of the maximal compact; and an open preconnected $O_\psi \subseteq \mathbb{C}$ containing the line $\mathrm{Re}\,s = 0$ and the half-plane $\mathrm{Re}\,s > 1/2$ together with $E_\psi, N_\psi$ analytic in $s$ on $O_\psi$ for each $g$, jointly continuous on $O_\psi \times \mathrm{GL}_2(\mathbb{A}_K)$, with $E_\psi(s,g) = \psi_s(g) + \sum_{\xi \in K} \psi_s(w\, n(\xi)\, g)$ and $N_\psi(s,g)$ equal to the Weyl intertwining integral $\int \psi_s(w^{-1} n(x) g)\,dx$ against the adelic additive Haar measure, both for $\mathrm{Re}\,s > 1/2$. For all real $t, R$ and all $x$ in the canonical truncation domain $\mathrm{canonicalTruncationDomain}\ K\ \alpha\ \beta$ with adelic height exceeding $e^{R}$, the truncation $\mathrm{lambdaT}$ of $g \mapsto E_\psi(it, g)$ at level $e^{R}$ — the function minus, on the set where the adelic height exceeds $e^{R}$, its constant term along $x \mapsto n(x)$ taken against the adelic additive Haar measure conditioned on the adelic box — satisfies $$\bigl|(\Lambda^{R} E_\psi(it))(x)\bigr| \le C\Bigl(1 + \sum_{v \mid \infty}\bigl(|t + \tau_\mu(v)| + |t - \tau_\nu(v)| + |m_\mu(v)| + |m_\nu(v)|\bigr)\Bigr)^{A} H(x)^{-N'},$$ with $H$ the adelic height. The measurable space and measure used in the truncation are those recorded in the fields `nS` and `ν` of `productionPinsOf`, namely the Borel structure on $\mathbb{A}_K$ and the adelic additive Haar measure conditioned on the adelic box; the remaining data entering `productionPinsOf` ($\Phi_K$, the principal level subgroups, the Hecke generators) do not affect the assertion.
--
--   This is the uniform form of the rapid-decay estimate for truncated Eisenstein series on $\mathrm{GL}_2$ over a number field: a single constant $C$ and exponent $A$ serve all unitary inducing data of the fixed level $N$ and the fixed archimedean types, with polynomial dependence on the spectral and weight parameters and arbitrarily fast decay in the adelic height. It is used to establish integrability of sums of convolutions of such truncated Eisenstein series against conjugates on the truncation domain, a step towards the spectral input of the trace-formula arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat.lean

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

theorem AutomorphicForm.forall_exists_forall_norm_lambdaT_axis_continuation_le_mul_pow_archParam_weight_mul_adelicHeight_rpow_neg_of_mem_canonicalTruncationDomain_of_flat
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
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ N' : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
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
      (t R : ℝ), ∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      Real.exp R < NumberField.AdelicHeight.adelicHeight K x →
      ‖(@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (Eψ ((t : ℂ) * Complex.I))) x‖ ≤
        C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
          NumberField.AdelicHeight.adelicHeight K x ^ (-(N' : ℝ)) := by sorry
