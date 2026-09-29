-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat
-- name    : AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/bc8347ea-d334-5c9c-9c49-d69ae132844e
-- title:
--   Flat sections: intertwining integral as completed L-ratio with axis bounds
-- statement:
--   Fix a number field $K$, together with a measurable-space and Borel structure on the idele group $(\mathbb{A}_K)^\times$ (here $\mathbb{A}_K$ denotes `AdeleRing (𝓞 K) K`), and the Borel $\sigma$-algebra on $\mathbb{A}_K$ itself. The central data consist of: a finite set $S_K$ of height-one primes of $\mathcal{O}_K$; a homomorphism $\xi_K$ from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated function on ideles is continuous (`hξc`) and trivial on the image of $K^\times$ (`hξt`); an ideal $N$ of $\mathcal{O}_K$ such that every prime $v$ with $v \mid N$ lies in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$, that is, a cardinality function on the infinite places of $K$ together with, for each infinite place $w$ and each index, a finite-dimensional complex representation of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$; and a real number $w$ such that $\|\xi_K(z)\| = \|z\|^{w}$ for all ideles $z$, where $\|z\| =$ [`NumberField.TateGlobal.ideleNorm K z`](def/NumberField_TateGlobalZeta.html#L19) is the module of $z$ (`hξw`).
--
--   The homomorphism $\alpha_m : (\mathbb{A}_K)^\times \to \mathbb{R}^\times$ is the unit-group homomorphism obtained from the distributive Haar character of $\mathbb{A}_K$ composed with the inclusion $\mathbb{R}_{\ge 0} \hookrightarrow \mathbb{R}$.
--
--   The assertion is the existence of a constant $C > 0$ and an exponent $A \in \mathbb{N}$, depending only on the above data, such that the following holds for all further data.
--
--   The further data and hypotheses are: positivity of $\alpha_m$ (`hαm`); two homomorphisms $\mu, \nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ that are unitary ($|\mu(x)| = |\nu(x)| = 1$ for all $x$), trivial on principal ideles (`IsIdeleClassChar`), and continuous as $\mathbb{C}$-valued functions, and satisfy $\mu(z)\nu(z)\|z\|^{w} = \xi_K(z)$ for all $z$; archimedean parameters $\tau^\mu, \tau^\nu : \mathrm{InfinitePlace}(K) \to \mathbb{R}$ such that, at each infinite place $v$ and each unit $x$ of $K_v$ whose image under the extension embedding is real and positive, the local character $\mu$ (respectively $\nu$) at $v$, obtained by restricting $\mu$ (respectively $\nu$) along the homomorphism placing a unit of $K_v$ in the $v$-component, equals $\|\cdot\|^{i\tau^\mu_v}$ (respectively $\|\cdot\|^{i\tau^\nu_v}$) evaluated at the module of the corresponding idele; and integer parameters $m^\mu, m^\nu : \mathrm{InfinitePlace}(K) \to \mathbb{Z}$ such that on the norm-one units of $K_v$ the same local characters are given by the $m^\mu_v$-th, respectively $m^\nu_v$-th, power of the extension embedding.
--
--   Next, a family $\psi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ is given, subject to the following group of hypotheses. For each $s$, $\psi_s$ is an induced section for the pair of characters $\eta_1(s) = \mu \cdot \alpha_m^{s + 1/2}$ and $\eta_2(s) = \nu \cdot \alpha_m^{-(s+1/2)}$, i.e. $\psi_s(bg) = \eta_1(s)(b_{11})\,\eta_2(s)(b_{22})\,\psi_s(g)$ for $b$ in the adelic Borel subgroup (`_hψf`); $\psi_s$ is archimedean $K$-finite, meaning that at each infinite place the right translates of $\psi_s$ under the archimedean row-isometry subgroup span a finite-dimensional space (`_hψfK`); $\psi_s$ is smooth for the finite adelic subgroup, i.e. its stabiliser in $\ker(\mathrm{gl}_{\mathrm{Arch}})$ under right translation is open (`_hψff`); $(s,g) \mapsto \psi_s(g)$ is jointly continuous (`_hψfjc`); $s \mapsto \psi_s(g)$ is entire for each $g$ (`_hψfhol`); at each infinite place there is a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup containing all the functions $k \mapsto \psi_s(gk)$ (`_hψfKu`); flatness, $\psi_s(k) = \psi_0(k)$ for all $s$ and all $k$ in the adelic maximal compact subgroup (`_hψfflat`); right invariance under the intersection of the principal level subgroup of level $N$ with the finite adelic subgroup (`_hψflev`); membership of $\psi_s$ in the archimedean cut submodule determined by $\mathrm{tys}_K$, i.e. the infimum over infinite places of the sums of the listed type submodules (`_hψfty`); and the normalisation $\int_{\mathbf{K}} \|\psi_0(k)\|^2 \, d k \le 1$ for the Haar measure on the adelic maximal compact subgroup $\mathbf{K}$ (`_hψfn`).
--
--   Finally, a set $O_\psi \subseteq \mathbb{C}$ and two functions $E_\psi, N_\psi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ are given, with the hypothesis `_hEψ` (nine clauses) requiring: $O_\psi$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$ the functions $s \mapsto E_\psi(s)(g)$ and $s \mapsto N_\psi(s)(g)$ are analytic on a neighbourhood of $O_\psi$; both are continuous on $O_\psi \times \mathrm{GL}_2(\mathbb{A}_K)$ jointly in $(s,g)$; on $\mathrm{Re}\,s > 1/2$, $E_\psi(s)(g) = \psi_s(g) + \sum_{\xi \in K} \psi_s(w_{\mathbb{A}} \, u(\xi) \, g)$ with $w_{\mathbb{A}}$ the adelic Weyl element and $u(\xi)$ the upper unipotent matrix; and on $\mathrm{Re}\,s > 1/2$, $N_\psi(s)(g) = \int_{\mathbb{A}_K} \psi_s(w_{\mathbb{A}}^{-1} u(x) g)\, dx$ against the adelic additive Haar measure.
--
--   The following auxiliary objects are then formed: $\chi = \mu\nu^{-1}$; the Euler product $P(w') = \prod_{v} \bigl(1 - a_v(\chi)\, (\mathrm{N}v)^{-w'}\bigr)^{-1}$ over height-one primes, where $a_v(\chi) = \chi(\varpi_v)$ at the places where $\chi$ is unramified in the sense of [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59) (the local character is trivial on the units of the ring of integers of the completion), $\varpi_v$ being the idele with a uniformiser at $v$, and $a_v(\chi) = 0$ otherwise, $\mathrm{N}v =$ `Ideal.absNorm v.asIdeal`; the archimedean factor
--   $$\gamma(w') = \prod_{v \text{ real}} \Gamma_{\mathbb{R}}\bigl(w' + i(\tau^\mu_v - \tau^\nu_v) + ((|m^\mu_v - m^\nu_v|) \bmod 2)\bigr) \prod_{v \text{ complex}} \Gamma_{\mathbb{C}}\bigl(w' + i(\tau^\mu_v - \tau^\nu_v) + |m^\mu_v - m^\nu_v|/2\bigr);$$
--   the constant $c$, the reciprocal of the real volume of the adelic box for the adelic additive Haar measure; and the weight function $D(y) = \sum_{v} \bigl(|y + \tau^\mu_v| + |y - \tau^\nu_v| + |m^\mu_v| + |m^\nu_v|\bigr)$, the sum over infinite places.
--
--   The conclusion asserts the existence of $\delta > 0$ and of a function $R : \mathbb{C} \to \mathbf{K} \to \mathbb{C}$ with the following five properties.
--
--   First, for each $k \in \mathbf{K}$ the function $s \mapsto R(s)(k)$ is analytic on a neighbourhood of $\{\mathrm{Re}\,s > -\delta\}$.
--
--   Second, $(s,k) \mapsto R(s)(k)$ is continuous on $\{\mathrm{Re}\,s > -\delta\} \times \mathbf{K}$.
--
--   Third, in the generic case: if $\chi$ is not equal to [`NumberField.TateGlobal.normPowChar K`](def/NumberField_NormPowChar.html#L22) $\tau_0$, i.e. to $z \mapsto \|z\|^{i\tau_0}$, for any real $\tau_0$, then for every entire $\Lambda : \mathbb{C} \to \mathbb{C}$ agreeing with $\gamma \cdot P$ on $\mathrm{Re}\,w' > 1$, and for every $s \in O_\psi$ with $\mathrm{Re}\,s > -\delta$ and every $k \in \mathbf{K}$,
--   $$\Lambda(2s+1)\,\bigl(c \cdot N_\psi(s)(k)\bigr) = \Lambda(2s)\, R(s)(k).$$
--
--   Fourth, in the exceptional case: for every real $\tau_0$ with $\chi = \|\cdot\|^{i\tau_0}$, and every entire $\Lambda_Q$ agreeing on $\mathrm{Re}\,w' > 1$ with $(w' + i\tau_0)(w' - (1 - i\tau_0))\,\gamma(w')P(w')$, one has for all $s \in O_\psi$ with $\mathrm{Re}\,s > -\delta$ and all $k \in \mathbf{K}$
--   $$(2s + i\tau_0 - 1)\,\Lambda_Q(2s+1)\,\bigl(c \cdot N_\psi(s)(k)\bigr) = (2s + i\tau_0 + 1)\,\Lambda_Q(2s)\,R(s)(k).$$
--
--   Fifth, the axis bounds: for every real $t$, both
--   $$\int_{\mathbf{K}} \|R(it)(k)\|^2\, dk \le \bigl(C (1 + D(t))^A\bigr)^2 \quad\text{and}\quad \int_{\mathbf{K}} \bigl\|\tfrac{d}{ds} R(s)(k)\big|_{s = it}\bigr\|^2 dk \le \bigl(C (1 + D(t))^A\bigr)^2,$$
--   the integrals being taken against the Haar measure on $\mathbf{K}$.
--
--   Note that $C$ and $A$ are chosen before $\mu, \nu$, the archimedean parameters and the section family, so that the bounds are uniform in those data, whereas $\delta$ and $R$ may depend on them.
--
--   This is the factorisation of the global $\mathrm{GL}_2$ intertwining operator on flat $K$-finite sections of fixed level and archimedean type: the Weyl intertwining integral, normalised by the volume of the adelic box, is the ratio $\Lambda(2s)/\Lambda(2s+1)$ of completed Hecke $L$-functions of $\chi = \mu\nu^{-1}$ times a normalised operator $R(s)$ which continues holomorphically slightly to the left of the unitary axis and whose $L^2(\mathbf{K})$-norm and axis derivative grow at most polynomially in the archimedean parameters. It combines the analytic continuation of the normalised operator with the two uniform $L^2$ bounds, and feeds the derivative estimate used in the spectral-side growth analysis of the Eisenstein contribution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
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

theorem AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat
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
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g)),
    let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ * ν⁻¹
    let P : ℂ → ℂ := fun w' => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w')))⁻¹
    let γ : ℂ → ℂ := fun w' => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs : ℕ) : ℂ) / 2))
    let c : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹
    let D : ℝ → ℝ := fun y => ∑ v : InfinitePlace K, (|y + τμ v| + |y - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))
    ∃ (δ : ℝ) (R : ℂ → adelicMaximalCompact K → ℂ), 0 < δ ∧
      (∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -δ < s.re}) ∧
      ContinuousOn (fun p : ℂ × adelicMaximalCompact K => R p.1 p.2) ({s : ℂ | -δ < s.re} ×ˢ Set.univ) ∧
      ((∀ τ₀ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar K τ₀) →
        ∀ (Λ : ℂ → ℂ), Differentiable ℂ Λ → (∀ w' : ℂ, 1 < w'.re → Λ w' = γ w' * P w') →
          ∀ s : ℂ, s ∈ Oψ → -δ < s.re → ∀ k : adelicMaximalCompact K,
            Λ (2 * s + 1) * (c * Nψ s (k : AdelicGL2 (𝓞 K) K)) = Λ (2 * s) * R s k) ∧
      (∀ τ₀ : ℝ, χ = NumberField.TateGlobal.normPowChar K τ₀ →
        ∀ (ΛQ : ℂ → ℂ), Differentiable ℂ ΛQ →
          (∀ w' : ℂ, 1 < w'.re → ΛQ w' = (w' + ((τ₀ : ℝ) : ℂ) * Complex.I) * (w' - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ w' * P w')) →
          ∀ s : ℂ, s ∈ Oψ → -δ < s.re → ∀ k : adelicMaximalCompact K,
            (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * ΛQ (2 * s + 1) * (c * Nψ s (k : AdelicGL2 (𝓞 K) K))
              = (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * ΛQ (2 * s) * R s k) ∧
      (∀ t : ℝ,
        (∫ k, ‖R ((t : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K)) ≤ (C * (1 + D t) ^ A) ^ 2 ∧
        (∫ k, ‖deriv (fun s : ℂ => R s k) ((t : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar K)) ≤ (C * (1 + D t) ^ A) ^ 2) := by sorry
