-- Prove2me | Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
-- name    : AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/bca7377a-d2b5-5ff8-8373-c806cea3e763
-- title:
--   Symmetric square-summable families approximated by Paley–Wiener coefficients
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha<\beta$, and $\Phi_K$ is a set of elements of $\mathrm{GL}_2$ of the adeles of $K$ entering as a parameter. The truncation domain is $D=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), and the carrier pins used throughout are $P=$ `productionPinsOf` for the domain $D$, the level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators $v\mapsto$ `heckeGen (𝓞 K) K v` and the box `adelicBox K`; thus $P$ carries the Borel structure and Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A}_K)$, the central subgroup $P.Z=\top$, and on the adele side the Haar measure conditioned to `adelicBox K`.
--
--   Geometric and measure-theoretic data. Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K\subset\mathrm{GL}_2(\mathbb{A}_K)$ are given such that `hcovK` holds: the union $\bigcup_{x\in T_K}(\,\cdot\,*x)$ of right translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ whose finite part lies in `finiteIntegralGL2`, whose local height at each infinite place is $\ge c_K$, whose window quantity `xWindowSq` at each infinite place is $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$) covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z$ in that union. Further, a Haar measure $\nu_{ZK}$ on the ideles is given together with a set $\Omega_K$ which is a fundamental domain (`hΩK`) for the range of $K^\times\to\mathbb{A}_K^\times$ acting on the ideles.
--
--   Central character and level. $S_K$ is a finite set of finite places; $\xi_K$ is a homomorphism from the full idele class group (the top subgroup) to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`), and of absolute value $1$ (`hξu`). An ideal $N$ of $\mathcal O_K$ is given with the property (`hN`) that every finite place dividing $N$ lies in $S_K$, and `tysK` is an `ArchTypeFamily K`, i.e. a finite list of archimedean types at each infinite place, cutting out the submodule `archCutSubmodule K tysK`. Writing $\alpha_m$ for the module character of $\mathbb{A}_K$ (the `distribHaarChar` of the adele ring, regarded as a homomorphism from the ideles to $\mathbb{R}^\times$), a hypothesis $h_{\alpha m}$ asserts $\alpha_m(x)>0$ for all $x$.
--
--   Cuspidal orthonormal family. A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ and Hecke eigensystems $\mathrm{cls}(i)$ over $\mathbb{C}$ are given, subject to: `hb`, each $\mathrm{cls}(i)$ lies in `cuspClasses K P ξK N SK` (level $N$, vanishing eigenvalues at the places of $S_K$, nonzero isotypic cuspidal submodule) and $b_i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}(i)$ intersected with `archCutSubmodule K tysK`; `hbn` and `hbo`, the $b_i$ are orthonormal for the inner product $\int_D b_i\overline{b_j}$ against the Haar measure; `hbs`, for each cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the isotypic cuspidal submodule of $\pi$ intersected with the archimedean cut; and `hbc`, completeness: any $\varphi$ which is a smooth cuspidal automorphic function for $P$ and $\xi_K$, continuous, right invariant under $P.U\,N$, in the archimedean cut, and orthogonal over $D$ to every $b_i$, vanishes almost everywhere on $D$.
--
--   Continuous-spectrum data. A countable type $\iota_E$ is given with families of characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ satisfying: unitarity, triviality on $K^\times$, continuity, the product relation $\mu_e\nu_e=\xi_K$, and separation (`_hdist`) of distinct indices already on the norm-one ideles. Integers $n_e$ and sections $\varphi_{e,j}(s,\cdot)$ are given satisfying the group of hypotheses: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the characters `etaFst (μ e) … s` $=\mu_e|\cdot|^{s+1/2}$ and `etaSnd (ν e) … s` $=\nu_e|\cdot|^{-(s+1/2)}$; each is archimedean $K$-finite and $K_f$-smooth; jointly continuous in $(s,g)$; entire in $s$ for fixed $g$; uniformly $K$-finite at each infinite place (a single finite-dimensional space of functions on the row-isometry subgroup containing all right translates); flat, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ on the maximal compact; invariant under the level group `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; contained in the archimedean cut; orthonormal on the maximal compact for `maximalCompactHaar K`; spanning (`_hφEspan`), in that every section of the same kind at $s=it$ lies in the span of the $\varphi_{e,j}(it,\cdot)$; and exhaustive (`_hpairs`), in that any unitary pair $(\mu',\nu')$ of idele class characters with $\mu'\nu'=\xi_K$ admitting a nonzero section of this kind at some $s=it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}$ are given with (`_hEE`) $O_{e,j}$ open, preconnected, containing the imaginary axis and the half-plane $\operatorname{Re}s>1/2$; $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ analytic on $O_{e,j}$ for each $g$, jointly continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_K)$; and, for $\operatorname{Re}s>1/2$, $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum'_{\xi\in K}\varphi_{e,j}(s,w\,u(\xi)g)$ with $w$ the adelic Weyl element and $u$ the unipotent embedding, while $N_{e,j}(s,g)$ is the Weyl intertwining integral `weylIntertwiningIntegral` of $\varphi_{e,j}(s,\cdot)$ at $g$ for the adelic additive Haar measure.
--
--   The coefficient family. Functions $F_{e,j}:\mathbb{R}\to\mathbb{C}$ are given with: `_hF2`, each $F_{e,j}\in L^2$; `_hFs`, summability of $e\mapsto\int_{\mathbb R}\sum_j\|F_{e,j}(t)\|^2$; and `_hFsym`, the symmetry under the functional equation: for all $e,\bar e$ and $\sigma\in\mathbb{R}$ with $\mu_{\bar e}=\nu_e\cdot$`normPowChar K σ` and $\nu_{\bar e}=\mu_e\cdot($`normPowChar K σ`$)^{-1}$, and for all $j$ and $t$,
--   $$F_{e,j}(t)=\sum_{j'<n_{\bar e}}\overline{\int_{\mathbf K}\bigl(\operatorname{vol}(\mathrm{adelicBox}\,K)^{-1}N_{e,j}(it,k)\bigr)\,\overline{\varphi_{\bar e,j'}\bigl(-i(t+\sigma),k\bigr)}\,dk}\;F_{\bar e,j'}\bigl(-(t+\sigma)\bigr),$$
--   the integral being over the maximal compact with `maximalCompactHaar K`. Finally $\varepsilon>0$ is given.
--
--   Conclusion. There exist a finite type $\iota_P$; characters $\mu_P,\nu_P:\iota_P\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ which are unitary, trivial on $K^\times$, continuous, and satisfy $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for all $z\in P.Z$; a map $r_P:\iota_P\to\iota_P$ with $\mu_P(r_Pe)=\nu_P(e)$ and $\nu_P(r_Pe)=\mu_P(e)$; a separation property for distinct indices on the norm-one ideles; a family of sections $\psi_e(s,\cdot)$ which are induced sections for `etaFst (μP e) … s` and `etaSnd (νP e) … s`, jointly continuous, entire in $s$, archimedean $K$-finite, $K_f$-smooth, uniformly $K$-finite at each infinite place, level-$N$ invariant and of the prescribed archimedean types, and which satisfy the Paley–Wiener decay condition `_hψdec`: for each $e$, each $n\in\mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_e(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$; a function $\psi$ which is a slab profile for the central subgroup and $\xi_K$ (measurable, invariant under left translation by unipotents and by rational Borel elements, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, and supported in a height band) and which is represented, for every $\sigma'$ and $g$, as $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it,g)\,dt$; maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu_{\mathrm{em}(i)}\cdot$`normPowChar K (τ i)` and $\nu_P(i)=\nu_{\mathrm{em}(i)}\cdot($`normPowChar K (τ i)`$)^{-1}$; and a function $p_\psi$ which is an automorphic function for $P$ and $\xi_K$, which is approximable in $L^2$ over $D$ by automorphic elements of the residual span (for every $\varepsilon'>0$ there is $r$ in [`AutomorphicForm.residualSpan`](def/AutomorphicForm_ResidualSpan.html#L12) — the span of the functions $g\mapsto\chi(\det g)$ for characters $\chi$ with $\chi^2=\xi_K$ on the centre — which is automorphic and has $\|p_\psi-r\|_{L^2(D)}<\varepsilon'$), and which is the residual projection of the pseudo-Eisenstein series in the sense that $\int_D(\mathrm{pseudoEisenstein}\,K\,\psi(g)-p_\psi(g))\overline{h(g)}\,dg=0$ for every automorphic $h$ in the residual span,
--
--   such that the following three assertions hold, where $\Theta(e,j,t)=\int_D \mathrm{pseudoEisenstein}\,K\,\psi(g)\,\overline{E_{e,j}(it,g)}\,dg$:
--
--   (i) for every $e\in\iota_E$ and $j<n_e$, the function $t\mapsto F_{e,j}(t)-\Theta(e,j,t)$ lies in $L^2(\mathbb{R})$;
--
--   (ii) the family $e\mapsto\int_{\mathbb{R}}\sum_{j<n_e}\|F_{e,j}(t)-\Theta(e,j,t)\|^2\,dt$ is summable;
--
--   (iii) $\sum'_{e\in\iota_E}\int_{\mathbb{R}}\sum_{j<n_e}\|F_{e,j}(t)-\Theta(e,j,t)\|^2\,dt\le\varepsilon^2$.
--
--   Note that the function subtracted from $F$ in (i)–(iii) is formed from the pseudo-Eisenstein series of $\psi$ itself, not from its difference with $p_\psi$; $p_\psi$ is produced only as the accompanying residual projection.
--
--   This is the density statement for the continuous part of the spectral decomposition of $L^2$ on $\mathrm{GL}_2$ over a number field: square-summable coefficient families that are symmetric under the functional equation of the Eisenstein family on the unitary axis are approximated, to within $\varepsilon$ in the global $\ell^2$-$L^2$ norm, by the Eisenstein coefficient families of matched Paley–Wiener pseudo-Eisenstein data of level $N$ and prescribed archimedean types. It feeds the companion statement [`AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_setIntegral_mul_conj_axis_continuation_sub_le`](thm.html#AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_setIntegral_mul_conj_axis_continuation_sub_le), which is used in assembling the spectral expansion on the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric.lean

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

theorem AutomorphicForm.exists_matched_paleyWiener_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le_of_symmetric
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
      (F : (e : ιE) → Fin (nE e) → ℝ → ℂ)
      (_hF2 : ∀ (e : ιE) (j : Fin (nE e)), MemLp (F e j) 2)
      (_hFs : Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖F e j t‖ ^ 2))
      (_hFsym : ∀ (e ē : ιE) (σ : ℝ),
        (μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
          ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹) →
        ∀ (j : Fin (nE e)) (t : ℝ),
          F e j t = ∑ j' : Fin (nE ē),
            conj (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
                  NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
                conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
              F ē j' (-(t + σ)))
      (ε : ℝ) (_hε : 0 < ε),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ =>
        F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e),
        ‖F e j t - (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ 2 ≤ ε ^ 2 := by sorry
