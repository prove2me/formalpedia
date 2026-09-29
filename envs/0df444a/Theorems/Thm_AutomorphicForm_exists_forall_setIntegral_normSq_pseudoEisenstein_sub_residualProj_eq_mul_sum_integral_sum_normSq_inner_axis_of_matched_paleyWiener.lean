-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/907c4990-4d8e-5ed1-b1f3-514ab275dfb2
-- title:
--   Plancherel identity for the continuous part in canonical Eisenstein coordinates
-- statement:
--   Let $K$ be a number field. Fix reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; the relevant region of $\mathrm{GL}_2$ over the adeles is the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the third component of the canonically chosen truncation datum attached to $(\alpha,\beta)$, and all global integrals are taken against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to that domain. The following further data are fixed: a set $\Phi_K$ of adelic matrices; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K$ of adelic matrices with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$, together with the hypothesis `hcovK` that the union over $x\in T_K$ of the right translates by $x$ of the centre-cut Siegel set $\{g:\ g$ has integral finite part, $c_K\le$ the local height at every infinite place, the $x$-window square is at most $u_K^2$ at every infinite place, and every archimedean determinant norm lies in $[d_{1K},d_{2K}]\}$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo $\mathrm{GL}_2(K)$ and the adelic centre; a Haar measure $\nu_{ZK}$ on the idele group with a set $\Omega_K$ that is a fundamental domain (`hΩK`) for the subgroup of principal ideles; a finite set $S_K$ of finite places; a character $\xi_K$ of the full idele group (presented as a homomorphism from $\top$ to $\mathbb{C}^\times$) which is continuous (`hξc`), trivial on principal ideles (`hξt`), and unitary (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every place dividing $N$ lies in $S_K$ (`hN`); and a family $\mathrm{tys}_K$ of archimedean types, i.e. for each infinite place a finite list of finite-dimensional representations of the row-isometry subgroup, cutting out the submodule `archCutSubmodule K tysK`.
--
--   Write $\alpha_m$ for the monoid homomorphism from the ideles to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ through $\mathbb{R}_{\ge0}\to\mathbb{R}$, and assume `hαm`, that $\alpha_m$ takes strictly positive values; the induced characters $\eta_1(\mu,s)=\mu\cdot\alpha_m^{s+1/2}$ and $\eta_2(\nu,s)=\nu\cdot\alpha_m^{-(s+1/2)}$ are `etaFst` and `etaSnd`. All automorphic notions are taken with respect to the carrier pins `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the canonical truncation domain as fundamental region, the full idele group as central subgroup $Z$, level subgroups $U(M)=\Gamma(M)\cap\ker(\text{archimedean projection})$, Hecke generators at the finite places, and the measure on $\mathbb{A}_K$ conditioned on the adelic box.
--
--   The assertion is the existence of a constant $\kappa$ with $0<\kappa$ such that the displayed identity holds for all data satisfying the following groups of hypotheses.
--
--   *Cuspidal orthonormal basis data.* A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` (a level, a proof that it is nonzero, and coefficient families $a,b$ indexed by the finite places), with: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses` for $\xi_K$, $N$, $S_K$ (level $N$, vanishing coefficients at the places of $S_K$, non-trivial isotypic cuspidal submodule) and each $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut; `hbn` and `hbo`, orthonormality of the $b\,i$ over the truncation domain; `hbs`, for each cuspidal class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the span of its $b$-images is exactly the $\pi$-isotypic cuspidal submodule intersected with the archimedean cut; and `hbc`, completeness: any continuous function that is smooth-cuspidal automorphic for $\xi_K$, right $U(N)$-invariant, in the archimedean cut and orthogonal to every $b\,i$ vanishes almost everywhere on the truncation domain.
--
--   *Eisenstein character family and its sections.* A countable type $\iota_E$ and characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ with the hypotheses (summarised here) that each $\mu_e,\nu_e$ is unitary, trivial on principal ideles and continuous, that $\mu_e\nu_e=\xi_K$, and that distinct indices are separated on the norm-one ideles. Natural numbers $n_E(e)$ and functions $\varphi_E(e,j,s,\cdot)$ with the hypotheses (summarised here) that each $\varphi_E(e,j,s)$ is an induced section for $\eta_1(\mu_e,s),\eta_2(\nu_e,s)$, is archimedean $K$-finite, is smooth for the finite-adelic subgroup, is jointly continuous in $(s,g)$, is holomorphic in $s$ pointwise, has uniformly finite-dimensional right translates under each archimedean row-isometry subgroup, is flat on the maximal compact subgroup (its value at $k$ equals the value at $s=0$), is right invariant under $\Gamma(N)\cap$ the finite-adelic subgroup, lies in the archimedean cut, is orthonormal over the maximal compact subgroup at $s=0$, and spans, for each real $t$, all induced sections at $s=it$ with these invariance and type properties (`_hφEspan`); and `_hpairs`, that every pair of unitary, ideleclass, continuous characters $(\mu',\nu')$ with $\mu'\nu'=\xi_K$ admitting a nonzero such section at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   *Axis continuations.* Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E,N_E$ with `_hEE`: each $O_E(e,j)$ is open, preconnected, contains the imaginary axis and the half-plane $\mathrm{Re}\,s>1/2$; $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$ for each $g$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$; and on $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E(e,j,s,w\,u(\xi)g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix, while $N_E(e,j,s,g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi_E(e,j,s,w^{-1}u(x)g)\,dx$ against `adelicAddHaar`.
--
--   *Paley–Wiener profile data.* A finite type $\iota_P$ and characters $\mu_P,\nu_P:\iota_P\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ with the hypotheses (summarised here) that each is unitary, trivial on principal ideles and continuous, that $\mu_P(e)\nu_P(e)=\xi_K$ on the central subgroup, that a map $r_P:\iota_P\to\iota_P$ interchanges $\mu_P$ and $\nu_P$, and that distinct indices are separated on the norm-one ideles. Sections $\psi_f(e,s,\cdot)$ with the hypotheses (summarised here) of being induced sections for $\eta_1(\mu_P(e),s),\eta_2(\nu_P(e),s)$, jointly continuous, holomorphic in $s$, archimedean $K$-finite, smooth for the finite-adelic subgroup, with uniformly finite-dimensional archimedean row-isometry translates, right $\Gamma(N)\cap$finite-adelic invariant and in the archimedean cut, and satisfying the vertical-strip decay bound `_hψdec`: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable bounded majorant $m$ with $(1+|t|)^n\|\psi_f(e,\sigma'+it,g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$ and $g\in C$. A function $\psi$ which is a slab profile for the central subgroup and $\xi_K$ (`_hψ`: measurable, invariant under left unipotent and under left translation by rational Borel elements, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, and supported where the adelic height lies in a band $[a,b]$ with $a>0$), together with `_hψrep`, the representation $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it,g)\,dt$ valid for every real $\sigma'$. A matching $e_m:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ with `_hem`: $\mu_P(i)=\mu(e_m i)\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P(i)=\nu(e_m i)\cdot\|\cdot\|^{-i\tau_i}$ in terms of `normPowChar`.
--
--   *Residual projection data.* A function $p_\psi$ which is automorphic for $\xi_K$ with respect to the pins (`_hpψ`), lies in the $L^2$-closure of the residual span in the sense of `_hpψc` (for every $\varepsilon>0$ there is an automorphic $r$ in `residualSpan`, the span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ with $\chi^2=\xi_K$ on the central subgroup, with $\|p_\psi-r\|_{L^2}<\varepsilon$ over the truncation domain), and is such that $\theta_\psi-p_\psi$ is orthogonal to every automorphic element of the residual span (`_hpψo`), where $\theta_\psi=$ `pseudoEisenstein K ψ` is $g\mapsto\psi(g)+\sum_{\beta\in K}\psi(w\,u(\beta)g)$.
--
--   The conclusion is the single identity
--   $$\int_{D}(\theta_\psi-p_\psi)\,\overline{(\theta_\psi-p_\psi)}\;=\;\kappa\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j<n_E(e_m i)}c_{i,j}(t)\,\overline{c_{i,j}(t)}\,dt,$$
--   where $D$ is the canonical truncation domain, the left integral is against `adelicGLHaar (Fin 2) (𝓞 K) K`, $\kappa$ is the real constant cast to $\mathbb{C}$, and
--   $$c_{i,j}(t)=\int_{\mathbf{K}}\psi_f(i,it,k)\,\overline{\varphi_E(e_m i,j,i(t+\tau_i),k)}\,dk\;+\;\int_{\mathbf{K}}\psi_f(r_P i,-it,k)\,\overline{v^{-1}N_E(e_m i,j,i(t+\tau_i),k)}\,dk,$$
--   the integrals being over the adelic maximal compact subgroup $\mathbf{K}$ against `maximalCompactHaar K`, and $v$ the real number `(adelicAddHaar (𝓞 K) K) (adelicBox K)` in $\mathbb{R}_{\ge0}^\infty$ converted to a real and cast to $\mathbb{C}$.
--
--   The hypotheses $\Phi_K$, $c_K,u_K,d_{1K},d_{2K},T_K$, `hcovK`, $\nu_{ZK}$, $\Omega_K$, `hΩK`, $S_K$ and `hN` enter only through the ambient setting fixed above.
--
--   This is the Plancherel identity for the continuous part of the truncated spectral decomposition, written in the canonical coordinates attached to the level-$N$ and archimedean-type families: the $L^2$-norm of a pseudo-Eisenstein series minus its residual projection is a positive multiple of the integral over the unitary axis of the squared lengths of the vectors of Bruhat-type pairings $c_{i,j}(t)$. It is used in the construction of matched Paley–Wiener profiles, where the identity furnishes the norm control needed to bound the non-residual part of a pseudo-Eisenstein series built from compactly supported smooth data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener
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
    ∃ κ : ℝ, 0 < κ ∧
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
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (κ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
        ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
                  conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                    NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
                  conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                    NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
