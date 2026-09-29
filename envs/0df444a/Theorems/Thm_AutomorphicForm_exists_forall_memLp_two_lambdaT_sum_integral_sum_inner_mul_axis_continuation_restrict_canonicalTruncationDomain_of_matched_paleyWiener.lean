-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/78230115-b26c-54f5-938d-3eba947be1c1
-- title:
--   L²-boundedness of the truncated Eisenstein wave packet
-- statement:
--   Throughout, $K$ is a number field, $\mathbb A =$ `AdeleRing (𝓞 K) K`, $G =$ `AdelicGL2 (𝓞 K) K` $= \mathrm{GL}_2(\mathbb A)$, the Haar measure on $G$ is `adelicGLHaar (Fin 2) (𝓞 K) K` for the Borel structure `glBorel`, and $D =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) is the canonical truncation domain attached to the real parameters $\alpha,\beta$ (the third component of the canonically chosen truncation datum). The abbreviation `pins` stands for `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the carrier data whose measurable space and measure on $G$ are the Borel structure and Haar measure above, whose domain is $D$, whose central subgroup is $\top \le \mathbb A^\times$, whose level subgroups are $\mathrm{principalLevel}(M)\sqcap$ `finiteAdelicGL2Subgroup K`, whose Hecke generators are `heckeGen (𝓞 K) K v`, and whose measure on $\mathbb A$ is the additive Haar measure conditioned on the adelic box `adelicBox K`. Writing $\mathrm i$ for the imaginary unit, for a real $T$ and $\varphi : G \to \mathbb C$ the truncation $\Lambda^{T}\varphi$ is [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with that conditioned measure on $\mathbb A$, the unipotent embedding $x \mapsto$ `unipotentGL2 x`, the height function [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and the cut-off $T$: it is $\varphi$ minus the indicator of $\{g : T < \mathrm{height}(g)\}$ times the constant term of $\varphi$ along the unipotent.
--
--   Geometric parameters. Real numbers $\alpha,\beta$ with $0 < \alpha$ and $\alpha < \beta$; a set $\Phi_K \subseteq G$, on which nothing is assumed; reals $c_K,u_K,d_{1K},d_{2K}$ with $0 < c_K$, $0 < d_{1K}$, $d_{1K} < d_{2K}$; a finite set $T_K \subseteq G$; and the covering hypothesis `hcovK`, namely that the union $\bigcup_{x \in T_K} (\cdot\, x)\,[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,]$ covers $G$ modulo the centre, i.e. for every $g \in G$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ (global point times $g$ times central scalar) in that union.
--
--   Central data. A measurable space and Borel structure on $\mathbb A^\times$, a Haar measure $\nu_{Z,K}$ on $\mathbb A^\times$, and a set $\Omega_K$ which is a fundamental domain for the range of $K^\times \to \mathbb A^\times$ acting on $\mathbb A^\times$ with respect to $\nu_{Z,K}$.
--
--   Character and level data. A finite set $S_K$ of height-one primes of $\mathcal O_K$; a homomorphism $\xi_K : \top \to \mathbb C^\times$ on the full idele unit group, whose associated function on $\mathbb A^\times$ is continuous (`hξc`), which is trivial on the image of $K^\times$ (`hξt`) and unitary (`hξu`); an ideal $N \subseteq \mathcal O_K$ such that every $v$ with $v \mid N$ lies in $S_K$; and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place a finite list of representations of the row-isometry group, cutting out the submodule `archCutSubmodule K tysK`.
--
--   The modulus character. $\alpha_m : \mathbb A^\times \to \mathbb R^\times$ is the unit-group homomorphism induced by `distribHaarChar` of $\mathbb A$ composed with $\mathbb R_{\ge 0} \to \mathbb R$, and $h_{\alpha m}$ asserts that all its values are positive; $\mathbb A$ carries the Borel structure `adeleBorel`. For a character $\mu$ and $s \in \mathbb C$, `etaFst μ αm hαm s` $= \mu \cdot \alpha_m^{s + 1/2}$ and `etaSnd ν αm hαm s` $= \nu \cdot \alpha_m^{-(s+1/2)}$.
--
--   Cuspidal orthonormal system. A type $\iota$, functions $b : \iota \to (G \to \mathbb C)$ and $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ` subject to: `hb`, each $\mathrm{cls}\,i$ is a cusp class for `pins`, $\xi_K$, $N$, $S_K$ (level $N$, both eigenvalue families vanishing on $S_K$, non-zero isotypic cuspidal submodule) and $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ intersected with `archCutSubmodule K tysK`; `hbn`, $\int_D b\,i\,\overline{b\,i} = 1$; `hbo`, $\int_D b\,i\,\overline{b\,j} = 0$ for $i \ne j$; `hbs`, for every cusp class $\pi$ the fibre $\{i : \mathrm{cls}\,i = \pi\}$ is finite and the $\mathbb C$-span of its image under $b$ equals the isotypic submodule of $\pi$ intersected with the archimedean cut; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for `pins` and $\xi_K$, continuous, invariant under right translation by `pins.U N`, lying in the archimedean cut, and orthogonal over $D$ to every $b\,i$, vanishes almost everywhere for Haar measure restricted to $D$.
--
--   Flat sections and Eisenstein data indexed by $\iota_E$. A countable type $\iota_E$ and families $\mu,\nu : \iota_E \to (\mathbb A^\times \to \mathbb C^\times)$ with: each $\mu\,e$, $\nu\,e$ unitary (`IsUnitaryChar`), trivial on principal ideles (`IsIdeleClassChar`), continuous; $\mu\,e \cdot \nu\,e = \xi_K$ pointwise; and distinct indices separated by some norm-one idele. Integers $n_E\,e$ and sections $\varphi_E\,e\,j\,s : G \to \mathbb C$ satisfying: each $\varphi_E\,e\,j\,s$ is an induced section for the pair $(\mathrm{etaFst}(\mu\,e)\,s,\ \mathrm{etaSnd}(\nu\,e)\,s)$ relative to the adelic Borel subgroup, archimedean $K$-finite, smooth for the finite part, jointly continuous in $(s,g)$, holomorphic in $s$ for each $g$, with a common finite-dimensional space of right translates under each archimedean row-isometry subgroup, flat on the maximal compact subgroup ($\varphi_E\,e\,j\,s\,k = \varphi_E\,e\,j\,0\,k$ there), invariant under $\mathrm{principalLevel}(N)\sqcap$ `finiteAdelicGL2Subgroup K`, lying in the archimedean cut, orthonormal over the maximal compact with respect to `maximalCompactHaar K` (`_hφEon`), spanning: every section at a point $t\mathrm i$ of the unitary axis with the same regularity, level and type properties lies in the span of the $\varphi_E\,e\,j\,(t\mathrm i)$ (`_hφEspan`); and `_hpairs`, exhaustion: for every pair of unitary, continuous idele class characters with product $\xi_K$ and every non-zero section at $t\mathrm i$ with those properties there is $e \in \iota_E$ agreeing with the pair on the norm-one ideles.
--
--   Analytic continuation data. Sets $O_E\,e\,j \subseteq \mathbb C$ and functions $E_E\,e\,j\,s, N_E\,e\,j\,s : G \to \mathbb C$ with the hypothesis `_hEE`: each $O_E\,e\,j$ is open, preconnected, contains the imaginary axis $\{\mathrm{re}\,s = 0\}$ and the half-plane $\{1/2 < \mathrm{re}\,s\}$; $s \mapsto E_E\,e\,j\,s\,g$ and $s \mapsto N_E\,e\,j\,s\,g$ are analytic on a neighbourhood of $O_E\,e\,j$ for each $g$; both are continuous on $O_E\,e\,j \times G$ jointly; for $\mathrm{re}\,s > 1/2$ one has $E_E\,e\,j\,s\,g = \varphi_E\,e\,j\,s\,g + \sum_{\xi \in K}' \varphi_E\,e\,j\,s\,(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element and $n$ the unipotent, and $N_E\,e\,j\,s\,g$ equals the Weyl intertwining integral $\int_{\mathbb A} \varphi_E\,e\,j\,s\,(w^{-1} n(x) g)$ against the adelic additive Haar measure.
--
--   Paley–Wiener datum indexed by $\iota_P$. A finite type $\iota_P$ with characters $\mu_P,\nu_P : \iota_P \to (\mathbb A^\times \to \mathbb C^\times)$, each unitary, an idele class character, continuous, with $\mu_P\,e \cdot \nu_P\,e = \xi_K$ on `pins.Z`; a map $r_P : \iota_P \to \iota_P$ exchanging the two families ($\mu_P(r_P e) = \nu_P e$, $\nu_P(r_P e) = \mu_P e$); separation of distinct indices by a norm-one idele; and functions $\psi_f\,e\,s : G \to \mathbb C$ which are induced sections for $(\mathrm{etaFst}(\mu_P e)\,s, \mathrm{etaSnd}(\nu_P e)\,s)$, jointly continuous, holomorphic in $s$, archimedean $K$-finite, smooth for the finite part, with a common finite-dimensional space of archimedean right translates, invariant under $\mathrm{principalLevel}(N)\sqcap$ `finiteAdelicGL2Subgroup K` and lying in the archimedean cut, and which satisfy the vertical-strip decay condition `_hψdec`: for each $e$, each $n \in \mathbb N$, each bound $\sigma_0$ and each compact $C \subseteq G$ there is an integrable, bounded $m : \mathbb R \to \mathbb R$ with $(1+|t|)^n\,\lVert \psi_f\,e\,(\sigma' + t\mathrm i)\,g \rVert \le m(t)$ for all $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$.
--
--   The profile and the matching. A function $\psi : G \to \mathbb C$ which is a slab profile for `pins.Z` and $\xi_K$ (measurable; invariant under left translation by unipotents and by global Borel points; transforming by $\xi_K$ under the centre; bounded on each slab where the idele norm of the determinant lies in $[d_1,d_2]$ with $d_1>0$; and non-vanishing only in a band of adelic heights), together with the representation `_hψrep`: for every $\sigma' \in \mathbb R$ and every $g$, $\psi(g) = \sum_{e} (4\pi)^{-1} \int_{\mathbb R} \psi_f\,e\,(\sigma' + t\mathrm i)\,g \,dt$. Finally maps $\mathrm{em} : \iota_P \to \iota_E$ and $\tau : \iota_P \to \mathbb R$ with $\mu_P\,i = \mu(\mathrm{em}\,i) \cdot \lVert\cdot\rVert^{\mathrm i \tau_i}$ and $\nu_P\,i = \nu(\mathrm{em}\,i) \cdot \lVert\cdot\rVert^{-\mathrm i \tau_i}$, where $\lVert\cdot\rVert^{\mathrm i t}$ is [`NumberField.TateGlobal.normPowChar K t`](def/NumberField_NormPowChar.html#L22).
--
--   Write, for $i \in \iota_P$, $j < n_E(\mathrm{em}\,i)$ and $t \in \mathbb R$,
--   $$c_{i,j}(t) = \int_{\mathbf K} \psi_f\,i\,(t\mathrm i)(k)\ \overline{\varphi_E\,(\mathrm{em}\,i)\,j\,((t+\tau_i)\mathrm i)(k)}\ d(\mathrm{maximalCompactHaar}\ K),$$
--   the integral being over the maximal compact subgroup `adelicMaximalCompact K`, and set
--   $$P(g) = \sum_{i \in \iota_P} \int_{\mathbb R} \sum_{j} c_{i,j}(t)\, E_E\,(\mathrm{em}\,i)\,j\,((t+\tau_i)\mathrm i)(g)\, dt .$$
--
--   Conclusion: there exists $R_0 \in \mathbb R$ such that for every real $R \ge R_0$ the following three assertions hold, all $L^2$-statements being with respect to Haar measure on $G$ restricted to $D$ and all truncations being $\Lambda^{\exp R}$ as described above.
--
--   First, the function
--   $$x \longmapsto \sum_{i \in \iota_P} \int_{\mathbb R} \sum_{j} c_{i,j}(t)\, \bigl(\Lambda^{\exp R} E_E\,(\mathrm{em}\,i)\,j\,((t+\tau_i)\mathrm i)\bigr)(x)\, dt$$
--   belongs to $L^2$; that is, the wave packet formed from the truncated Eisenstein series is square-integrable on $D$.
--
--   Second, for every $x \in D$ the truncation of the packet agrees at $x$ with the packet of truncations:
--   $$\bigl(\Lambda^{\exp R} P\bigr)(x) = \sum_{i \in \iota_P} \int_{\mathbb R} \sum_{j} c_{i,j}(t)\, \bigl(\Lambda^{\exp R} E_E\,(\mathrm{em}\,i)\,j\,((t+\tau_i)\mathrm i)\bigr)(x)\, dt .$$
--
--   Third, the truncated packet $x \mapsto (\Lambda^{\exp R} P)(x)$ itself belongs to $L^2$ for the same restricted measure.
--
--   This is the square-integrability statement for the truncated Eisenstein wave packet built from a matched Paley–Wiener datum: the truncation operator may be pulled inside the $t$-integral on the truncation domain, and both the packet of truncations and the truncation of the packet lie in $L^2$ of the truncation domain. It feeds the analysis of the continuous part of the spectral decomposition of $\mathrm{GL}_2$ over a number field, and is cited by [`AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_forall_memLp_two_lambdaT_sum_integral_sum_inner_mul_axis_continuation_restrict_canonicalTruncationDomain_of_matched_paleyWiener
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
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      MemLp (fun x : AdelicGL2 (𝓞 K) K =>
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
      (∀ x ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x =
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) *
            @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I)) x) ∧
      MemLp (fun x : AdelicGL2 (𝓞 K) K =>
          @AutomorphicForm.lambdaT _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).nS _ _ (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν
          (fun n => AutomorphicForm.unipotentGL2 n) (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun g : AdelicGL2 (𝓞 K) K =>
            ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                ∂(maximalCompactHaar K)) * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
