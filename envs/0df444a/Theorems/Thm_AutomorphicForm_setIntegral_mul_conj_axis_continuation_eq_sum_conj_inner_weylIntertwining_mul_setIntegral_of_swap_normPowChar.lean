-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_axis_continuation_eq_sum_conj_inner_weylIntertwining_mul_setIntegral_of_swap_normPowChar
-- name    : AutomorphicForm.setIntegral_mul_conj_axis_continuation_eq_sum_conj_inner_weylIntertwining_mul_setIntegral_of_swap_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e801e9fd-f338-5e07-a3b5-4b0d38ccb358
-- title:
--   Symmetry of Eisenstein coefficients under the axis functional equation
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$, and $D:=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the canonical truncation domain attached to the window $[\alpha,\beta]$; integration over $\mathrm{GL}_2(\mathbb{A}_K)$ is with respect to `adelicGLHaar (Fin 2) (𝓞 K) K` and the Borel $\sigma$-algebra. A set $\Phi_K$ of adelic $\mathrm{GL}_2$-points is among the binders; nothing is assumed of it and it does not occur in the conclusion.
--
--   Siegel-covering data: reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$, a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$, and the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}(\,\cdot\,x)\big[\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}\big]$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central idele $z$ with $\gamma g z$ in that union; the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c_K$, whose $x$-window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$.
--
--   Central data: the idele units $(\mathbb{A}_K)^\times$ carry a measurable structure which is Borel, $\nu_{ZK}$ is a Haar measure on them, and $\Omega_K$ is a fundamental domain (`hΩK`) for the subgroup of principal ideles, the range of $K^\times\to(\mathbb{A}_K)^\times$, with respect to $\nu_{ZK}$. Further, $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full subgroup of idele units to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and of absolute value $1$ (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ such that every finite place whose prime divides $N$ lies in $S_K$ (`hN`); and $\mathrm{tys}_K$ is an archimedean type family, assigning to each infinite place $w$ a finite list of representations of the row-isometry subgroup of $K_w$.
--
--   The statement then introduces $\alpha_m$, the module character `distribHaarChar` of $\mathbb{A}_K$ read as a homomorphism $(\mathbb{A}_K)^\times\to\mathbb{R}^\times$, together with the hypothesis `hαm` that $\alpha_m(x)>0$ for all $x$, and fixes the Borel $\sigma$-algebra on $\mathbb{A}_K$. Write $\mathrm{pins}$ for `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier data with domain $D$, adelic $\mathrm{GL}_2$ Haar measure, full central subgroup, level subgroups $\Gamma(M)\cap\ker(\mathrm{gl}_{\mathrm{arch}})$, Hecke generators $\mathrm{heckeGen}_v$, and additive measure the adelic Haar measure conditioned on the box `adelicBox K`.
--
--   Discrete-spectrum basis package: a type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$, subject to: `hb`, each $\mathrm{cls}(i)$ is a cusp class for $(\mathrm{pins},\xi_K,N,S_K)$ — level $N$, vanishing Hecke and central parameters at the places of $S_K$, non-zero isotypic cuspidal submodule — and $b_i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`; `hbn`, $\int_D b_i\overline{b_i}=1$; `hbo`, $\int_D b_i\overline{b_j}=0$ for $i\ne j$; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic submodule of $\pi$ cut by the archimedean types; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $(\mathrm{pins},\xi_K)$, continuous, right invariant under $\mathrm{pins}.U\,N$, of the prescribed archimedean types, and orthogonal over $D$ to every $b_i$, vanishes almost everywhere on $D$ for the restriction of the $\mathrm{GL}_2$ Haar measure to $D$.
--
--   Eisenstein family package: a countable index type $\iota_E$; families of characters $\mu,\nu:\iota_E\to\big((\mathbb{A}_K)^\times\to\mathbb{C}^\times\big)$ with, for every $e$, $\mu_e,\nu_e$ unitary (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), with $\mu_e\nu_e=\xi_K$ (`_hμν`), and distinct indices separated on the norm-one ideles (`_hdist`). Integers $n_E(e)$ and sections $\varphi_{e,j}(s)$ for $j<n_E(e)$ are given, subject to the hypotheses (summarised here, one clause each): each $\varphi_{e,j}(s)$ is an induced section for the pair $\big(\mu_e\,\alpha_m^{\,s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\big)$ in the sense of `IsInducedSection` (`_hφE`), is archimedean $K$-finite (`_hφEK`) and smooth for the finite part (`_hφEf`), jointly continuous in $(s,g)$ (`_hφEjc`), holomorphic in $s$ for each $g$ (`_hφEhol`), with $K$-finiteness uniform in $s$ through one finite-dimensional space per infinite place (`_hφEKu`), independent of $s$ on the adelic maximal compact (`_hφEflat`), invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{gl}_{\mathrm{arch}})$ (`_hφElev`), of the prescribed archimedean types (`_hφEty`), orthonormal on the maximal compact for `maximalCompactHaar` (`_hφEon`), spanning at each point $it$ of the unitary axis all sections with these properties (`_hφEspan`), and `_hpairs`, exhaustiveness: for every pair of unitary continuous idele class characters $\mu',\nu'$ with $\mu'\nu'=\xi_K$ and every non-zero section $\varphi_0$ of the corresponding type at $s=it$, some index $e$ has $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles. Finally, domains $O_E(e,j)\subseteq\mathbb{C}$ and families $E_{e,j}(s,\cdot)$, $N_{e,j}(s,\cdot)$ are given, with `_hEE` asserting: $O_E(e,j)$ is open, preconnected, and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansion $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\big(s,\,w\,u(\xi)\,g\big)$ with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent; and for $\mathrm{Re}\,s>1/2$, $N_{e,j}(s,g)$ is the Weyl intertwining integral of $\varphi_{e,j}(s)$ at $g$ against the adelic additive Haar measure.
--
--   Test function and swap data: $\Psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ is measurable, vanishes off some compact set, and is bounded; indices $e,\bar e\in\iota_E$ and a real $\sigma$ satisfy `_hsw`, namely $\mu_{\bar e}=\nu_e\cdot\|\cdot\|^{i\sigma}$ and $\nu_{\bar e}=\mu_e\cdot\|\cdot\|^{-i\sigma}$, where $\|\cdot\|^{i\sigma}$ is [`NumberField.TateGlobal.normPowChar K σ`](def/NumberField_NormPowChar.html#L22); and $j<n_E(e)$, $t\in\mathbb{R}$ are fixed.
--
--   Let $\theta_\Psi$ denote the $\xi_K$-twisted central automorphisation of the truncated $\Psi$,
--   $$\theta_\Psi(g)=\sum_{q\in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}^{\ \mathrm{f}}\ \int_{(\mathbb{A}_K)^\times}\xi_K(w)^{-1}\,\big(\mathbf 1_D\Psi\big)\big(z(w)\,\gamma_q\,g\big)\,d\nu_{ZK}(w),$$
--   the outer sum being the finsum over the coset space, $\gamma_q$ the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of a chosen representative of $q$, $z(w)$ the central scalar matrix of $w$, and $\mathbf 1_D\Psi$ the indicator of $D$ applied to $\Psi$.
--
--   The conclusion is the identity
--   $$\int_D \theta_\Psi(g)\,\overline{E_{e,j}(it,g)}\;d\mu_{\mathrm{GL}} \;=\; \sum_{j'<n_E(\bar e)} \overline{\left(\int_{\mathbf K} \mathrm{vol}(\mathrm{adelicBox}\,K)^{-1}\,N_{e,j}(it,k)\;\overline{\varphi_{\bar e,j'}\big(-i(t+\sigma),k\big)}\,d k\right)}\ \cdot \int_D \theta_\Psi(g)\,\overline{E_{\bar e,j'}\big(-i(t+\sigma),g\big)}\;d\mu_{\mathrm{GL}},$$
--   where $it=(t:\mathbb{C})\cdot i$, the inner integral is over `adelicMaximalCompact K` against `maximalCompactHaar K`, and $\mathrm{vol}(\mathrm{adelicBox}\,K)$ is the real number obtained from the adelic additive Haar measure of the box. Thus the Eisenstein coefficients of $\theta_\Psi$ at $(e,j,it)$ are expressed as the conjugate-intertwining combination of its coefficients at $(\bar e,j',-i(t+\sigma))$.
--
--   This is the pairing of the functional equation of the Eisenstein continuations on the unitary axis against the $\xi_K$-twisted central automorphisation of a bounded, compactly supported $\Psi$: it transports the relation between $E_{e,j}(it)$ and the family $E_{\bar e,j'}(-i(t+\sigma))$, with kernel the Weyl intertwining coefficients, to the spectral coefficients of $\theta_\Psi$ over the truncation domain $D$. It is used in the Paley–Wiener matching estimate [`AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_setIntegral_mul_conj_axis_continuation_sub_le`](thm.html#AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_setIntegral_mul_conj_axis_continuation_sub_le), where the continuous part of the spectral expansion must be counted once per symmetry orbit $(e,t)\sim(\bar e,-(t+\sigma))$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_axis_continuation_eq_sum_conj_inner_weylIntertwining_mul_setIntegral_of_swap_normPowChar.lean

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
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_mul_conj_axis_continuation_eq_sum_conj_inner_weylIntertwining_mul_setIntegral_of_swap_normPowChar
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
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
      (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
      (_hΨb : ∃ M : ℝ, ∀ y, ‖Ψ y‖ ≤ M)
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ),
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∑ j' : Fin (nE ē),
        conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g * conj (EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
