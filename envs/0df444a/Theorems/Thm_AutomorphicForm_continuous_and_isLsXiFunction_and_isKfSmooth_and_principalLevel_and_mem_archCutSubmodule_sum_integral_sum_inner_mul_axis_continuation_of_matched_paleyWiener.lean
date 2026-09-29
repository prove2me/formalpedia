-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- name    : AutomorphicForm.continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/25d6188a-9013-5972-8b53-1e0df7656701
-- title:
--   Regularity of the unitary-axis Eisenstein wave packet
-- statement:
--   Throughout, $K$ is a number field and $\mathcal P$ denotes the carrier pins `productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: its measurable space and measure on $\mathrm{GL}_2(\mathbb A_K)$ are the Borel structure and the Haar measure `adelicGLHaar`, its domain is the canonical truncation domain attached to the parameters $\alpha,\beta$, its central subgroup is $\mathcal P.Z=\top$ (all ideles), its level subgroups are $\mathcal P.U\,M=\mathrm{principalLevel}(M)\sqcap\ker(\mathrm{gl}_{\mathrm{arch}})$, its Hecke generators are the `heckeGen` elements, and its additive measure is the adelic additive Haar measure conditioned on the box `adelicBox K`.
--
--   The geometric parameters are real numbers $\alpha<\beta$ with $0<\alpha$, a set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb A_K)$ to which no hypothesis is attached, real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$, and a finite set $T_K$ of adelic matrices such that the union of the right translates $(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}]$, $x\in T_K$, covers $\mathrm{GL}_2(\mathbb A_K)$ modulo the centre in the sense of `CoversModCentre` (for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ in that union); here the centre-cut Siegel set consists of the $g$ whose finite part is integral, whose archimedean components have local height $\ge c_K$ and $x$-window square $\le u_K^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. On the idele group a measurable and Borel structure, a Haar measure $\nu_{Z_K}$ and a set $\Omega_K$ are given, $\Omega_K$ being a fundamental domain for the subgroup of principal ideles (the range of $K^\times\to\mathbb A_K^\times$).
--
--   The arithmetic data are a finite set $S_K$ of finite places, a homomorphism $\xi_K$ from the full subgroup of ideles to $\mathbb C^\times$ which is continuous, unitary ($|\xi_K(z)|=1$ for all $z$) and trivial on principal ideles, an ideal $N\subseteq\mathcal O_K$ all of whose prime divisors lie in $S_K$, and an archimedean type family $\mathcal T_K$ (for each infinite place $w$ a number $\mathcal T_K.\mathrm{card}\,w$ of representations of the row-isometry group at $w$). Write $\alpha_m$ for the positive real character of the idele group obtained from the distributive Haar character (the idele module), and $h_{\alpha m}$ for the hypothesis that $\alpha_m$ takes positive values; the adelic Borel structure is in force.
--
--   A cuspidal orthonormal family is then given: a type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ and Hecke eigensystems $\mathrm{cls}_i$ over $\mathbb C$, subject to: `hb`, each $\mathrm{cls}_i$ lies in $\mathrm{cuspClasses}\,K\,\mathcal P\,\xi_K\,N\,S_K$ (level $N$, vanishing $a_v,b_v$ at $v\in S_K$, non-zero isotypic cusp submodule) and $b_i$ lies in the intersection of the isotypic cusp submodule of $\mathrm{cls}_i$ with the archimedean cut submodule $\mathrm{archCutSubmodule}\,K\,\mathcal T_K$ (the intersection over infinite places $w$ of the supremum of the type submodules of the representations $\mathcal T_K.\mathrm{rep}\,w\,i$); `hbn` and `hbo`, the $b_i$ are orthonormal for the integral of $b_i\overline{b_j}$ over the canonical truncation domain against `adelicGLHaar`; `hbs`, for every class $\pi$ in $\mathrm{cuspClasses}$ the fibre $\{i\mid \mathrm{cls}_i=\pi\}$ is finite and the $\mathbb C$-span of its image under $b$ equals the isotypic cusp submodule of $\pi$ cut by $\mathrm{archCutSubmodule}\,K\,\mathcal T_K$; and `hbc`, completeness: every $\varphi$ which satisfies the predicate `IsSmoothCuspAutomorphicFnAt` for $\mathcal P$ and $\xi_K$ (cuspidal automorphic in the sense of `IsCuspAutomorphicFnAt` together with $K_f$-smoothness, i.e. being a smooth vector for the finite-adelic subgroup $\ker(\mathrm{gl}_{\mathrm{arch}})$), is continuous, is right invariant under $\mathcal P.U\,N$, lies in the archimedean cut submodule and is orthogonal over the truncation domain to every $b_i$, vanishes almost everywhere for `adelicGLHaar` restricted to that domain.
--
--   Next the continuous-spectrum data. A countable type $\iota_E$ and families of characters $\mu_e,\nu_e$ of the idele group are given, with the hypotheses (unitarity, triviality on $K^\times$, continuity, $\mu_e\nu_e=\xi_K$, and pairwise separation on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16)). For each $e$ there are $n_e\in\mathbb N$ and sections $\varphi_{e,j,s}$, $j\in\mathrm{Fin}(n_e)$, subject to a group of hypotheses: each $\varphi_{e,j,s}$ is an induced section for the pair $(\mu_e\,\alpha_m^{\,s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)})$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $K$-finite and $K_f$-smooth; $(s,g)\mapsto\varphi_{e,j,s}(g)$ is continuous and $s\mapsto\varphi_{e,j,s}(g)$ is entire; at each infinite place the right translates under the row-isometry subgroup lie in one fixed finite-dimensional space, uniformly in $s$ and $g$; the sections are flat, $\varphi_{e,j,s}(k)=\varphi_{e,j,0}(k)$ on the adelic maximal compact subgroup; they are right invariant under $\mathrm{principalLevel}(N)\sqcap\ker(\mathrm{gl}_{\mathrm{arch}})$ and lie in the archimedean cut submodule; at $s=0$ they are orthonormal on the maximal compact subgroup for `maximalCompactHaar`; and (`_hφEspan`) for every $e$ and $t\in\mathbb R$ every continuous, archimedean $K$-finite, level-$N$, type-compatible induced section at $s=\mathrm{i}t$ lies in the span of the $\varphi_{e,j,\mathrm{i}t}$. The hypothesis `_hpairs` asserts the exhaustion: any pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$ carrying a non-zero continuous archimedean $K$-finite level-$N$ type-compatible induced section on the unitary axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   The continuation data consist of sets $O_{e,j}\subseteq\mathbb C$ and families $E_{e,j},N_{e,j}$, with `_hEE` (nine clauses): each $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for every $g$ the functions $s\mapsto E_{e,j}(s)(g)$ and $s\mapsto N_{e,j}(s)(g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb A_K)$ jointly; for $\operatorname{Re}s>1/2$, $E_{e,j}(s)(g)=\varphi_{e,j,s}(g)+\sum_{\xi\in K}\varphi_{e,j,s}(w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u(\cdot)$ the upper unipotent; and for $\operatorname{Re}s>1/2$, $N_{e,j}(s)(g)$ is the Weyl intertwining integral $\int\varphi_{e,j,s}(w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure.
--
--   Finally the matched Paley–Wiener datum: a finite type $\iota_P$, characters $\mu_{P,e},\nu_{P,e}$ which are unitary, trivial on $K^\times$, continuous, satisfy $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for all $z\in\mathcal P.Z$, are pairwise separated on the norm-one ideles, and are permuted by a map $r_P$ interchanging $\mu_P$ and $\nu_P$; section families $\psi_{e,s}$ which are induced sections for $(\mu_{P,e}\alpha_m^{s+1/2},\nu_{P,e}\alpha_m^{-(s+1/2)})$, jointly continuous, entire in $s$, archimedean $K$-finite, $K_f$-smooth, uniformly $K$-finite at each infinite place, right invariant under $\mathrm{principalLevel}(N)\sqcap\ker(\mathrm{gl}_{\mathrm{arch}})$, lying in the archimedean cut submodule, and rapidly decreasing in the sense of `_hψdec`: for every $e$, $n\in\mathbb N$, $\sigma_0$ and compact $C$ there is an integrable bounded $m:\mathbb R\to\mathbb R$ with $(1+|t|)^n\|\psi_{e,\sigma'+\mathrm{i}t}(g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$, $t\in\mathbb R$, $g\in C$. A function $\psi$ is given which is a slab profile for $\mathcal P.Z$ and $\xi_K$ (measurable, invariant under left unipotent and global Borel translations, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, and supported in an adelic height band) and which satisfies $\psi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb R}\psi_{e,\sigma'+\mathrm{i}t}(g)\,dt$ for every $\sigma'\in\mathbb R$ and every $g$. The matching is given by $em:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb R$ with $\mu_{P,i}=\mu_{em(i)}\cdot\|\cdot\|^{\mathrm{i}\tau_i}$ and $\nu_{P,i}=\nu_{em(i)}\cdot\|\cdot\|^{-\mathrm{i}\tau_i}$, where $\|\cdot\|^{\mathrm{i}t}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   Let $P$ be the wave packet
--   $$P(g)=\sum_{i\in\iota_P}\int_{\mathbb R}\sum_{j\in\mathrm{Fin}(n_{em(i)})}\Big(\int_{\mathbf K}\psi_{i,\mathrm{i}t}(k)\,\overline{\varphi_{em(i),j,\mathrm{i}(t+\tau_i)}(k)}\,d\,\mathrm{maximalCompactHaar}\Big)\,E_{em(i),j}\big(\mathrm{i}(t+\tau_i)\big)(g)\,dt,$$
--   the inner integral being taken over the adelic maximal compact subgroup.
--
--   The conclusion is the conjunction of five assertions: $P$ is continuous; $P$ satisfies `IsLsXiFunction` for $\mathcal P.Z$ and $\xi_K$, that is $P(\gamma g)=P(g)$ for every $\gamma\in\mathrm{GL}_2(K)$ mapped into $\mathrm{GL}_2(\mathbb A_K)$ and $P(z\,g)=\xi_K(z)P(g)$ for every idele $z$ acting through the central scalar embedding; $P$ is $K_f$-smooth; $P(gu)=P(g)$ for every $g$ and every $u\in\mathcal P.U\,N=\mathrm{principalLevel}(\mathcal O_K,K,N)\sqcap\mathrm{finiteAdelicGL2Subgroup}\,K$; and $P$ lies in the archimedean cut submodule $\mathrm{archCutSubmodule}\,K\,\mathcal T_K$.
--
--   This is the algebraic and topological regularity statement for the Eisenstein wave packet formed on the unitary axis from a Paley–Wiener datum matched to a flat family of induced sections, in Langlands' spectral theory for $\mathrm{GL}_2$ over a number field in adelic form: the packet is automorphic with central character $\xi_K$, smooth at the finite places, of level $N$ and of the prescribed archimedean types. Together with the separate square-integrability statement on the canonical truncation domain it feeds the one-term wave-packet representation of a pseudo-Eisenstein series modulo its residual projection.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    let P : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g
    Continuous P ∧
      AutomorphicForm.IsLsXiFunction (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK P ∧
      IsKfSmooth K P ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, P (g * u) = P g) ∧
      P ∈ archCutSubmodule K tysK := by sorry
