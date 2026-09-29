-- Prove2me | Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/53b7a945-8684-5ca6-8071-0316c332c9bf
-- title:
--   Merging two matched Paley–Wiener packets with three-way decompositions
-- statement:
--   Throughout, $K$ is a number field, $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$, and $\Phi_0 :=$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) denotes the domain component of the canonically chosen truncation datum attached to $(\alpha,\beta)$, a subset of $\mathrm{GL}_2$ of the adele ring of $K$ (written `AdelicGL2 (𝓞 K) K`). All integrals over $\Phi_0$ are taken against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2(\mathbb{A}_K)$. The carrier data used throughout is the structure
--   $$P := \mathtt{productionPinsOf}\,K\,\Phi_0\,\bigl(M \mapsto \mathtt{principalLevel}\,(𝓞 K)\,K\,M \sqcap \mathtt{finiteAdelicGL2Subgroup}\,K\bigr)\,\bigl(v \mapsto \mathtt{heckeGen}\,(𝓞 K)\,K\,v\bigr)\,(\mathtt{adelicBox}\,K),$$
--   whose Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ are the standard ones, whose domain is $\Phi_0$, whose central subgroup $P.Z$ is all of $\mathbb{A}_K^{\times}$, whose level subgroups are $U(M) = \mathtt{principalLevel}(M) \sqcap \ker(\mathtt{glArch})$, whose Hecke elements are the `heckeGen` matrices, and whose additive measure $P.\nu$ is the adelic additive Haar measure conditioned on the adelic box.
--
--   Geometric and central frame. A set $\Phi_K$ of adelic matrices is given, on which no condition is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K$ of adelic matrices are given, subject to `hcovK`: the union $\bigcup_{x\in T_K}(\cdot\,{*}\,x)''\,\mathtt{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\, z \in$ that union, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose local heights at all infinite places are $\ge c_K$, whose $x$-window squares are $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. A measurable and Borel structure on the idele units is fixed together with a Haar measure $\nu_{Z K}$ and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the image of $K^{\times}$ in the ideles. A finite set $S_K$ of finite places, a character $\xi_K$ of the full unit group $\mathbb{A}_K^{\times}$ with values in $\mathbb{C}^{\times}$, continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary (`hξu`), an ideal $N$ of $𝓞 K$ with every prime dividing $N$ lying in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$ (a number of representations of the row-isometry subgroup at each infinite place, whose associated cut submodule is `archCutSubmodule K tysK`) are given. Finally $\alpha_m$ denotes the $\mathbb{R}^{\times}$-valued character obtained from the distributive Haar character of $\mathbb{A}_K$, and `hαm` asserts its positivity; the adele ring carries its Borel $\sigma$-algebra.
--
--   Cuspidal basis data. A type $\iota$, functions $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ and $\mathrm{cls} : \iota \to \mathtt{HeckeEigensystem}\,K\,\mathbb{C}$ are given with: `hb`, each $\mathrm{cls}\,i$ is a cusp class for $(P,\xi_K,N,S_K)$ (its level is $N$, its $a$- and $b$-eigenvalues vanish on $S_K$, and its isotypic cuspidal submodule is nonzero) and $b\,i$ lies in the isotypic cuspidal submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut submodule; `hbn`, $\int_{\Phi_0} b\,i\cdot\overline{b\,i} = 1$; `hbo`, $\int_{\Phi_0} b\,i\cdot\overline{b\,j} = 0$ for $i \neq j$; `hbs`, for each cusp class $\pi$ the fibre $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the $\mathbb{C}$-span of $b$ over it equals the isotypic cuspidal submodule of $\pi$ intersected with the archimedean cut; and `hbc`, any $\varphi$ which is a smooth cuspidal automorphic function for $(P,\xi_K)$, continuous, right $U(N)$-invariant, in the archimedean cut and orthogonal over $\Phi_0$ to every $b\,i$ vanishes almost everywhere on $\Phi_0$.
--
--   Eisenstein family data. A countable type $\iota_E$ and families $\mu,\nu : \iota_E \to (\mathbb{A}_K^{\times} \to \mathbb{C}^{\times})$ are given, each member unitary, trivial on principal ideles, continuous, with $\mu_e \nu_e = \xi_K$, and separated on the norm-one ideles (the kernel of the distributive Haar character) in the sense that distinct indices are distinguished there by $\mu$ or by $\nu$. Together with multiplicities $n_E : \iota_E \to \mathbb{N}$ there are section families $\varphi_E e j : \mathbb{C} \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ subject to a block of hypotheses (summarised here): each $\varphi_E e j s$ is an induced section for the pair of characters $\bigl(\mu_e\,\|\cdot\|^{s+1/2},\ \nu_e\,\|\cdot\|^{-(s+1/2)}\bigr)$ built from $\alpha_m$, that is $\varphi(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $K$-finite, smooth for the finite-adelic subgroup, jointly continuous in $(s,g)$, entire in $s$ for each $g$, uniformly $K$-finite at each infinite place (a single finite-dimensional space of functions on the row-isometry subgroup containing all right translates, for all $s$ and $g$), flat on the maximal compact subgroup ($\varphi_E e j s(k) = \varphi_E e j 0(k)$), right invariant under $U(N)$, contained in the archimedean cut, and orthonormal in $j$ against the Haar measure of the maximal compact subgroup; moreover `_hφEspan` asserts that any section on the line $s = it$ with the same invariance properties lies in the span of the $\varphi_E e j(it)$, and `_hpairs` asserts that every unitary idele-class pair $(\mu',\nu')$ with $\mu'\nu' = \xi_K$ carrying a nonzero such section on a line $s = it$ agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Domains $O_E e j \subseteq \mathbb{C}$ and families $E_E, N_E$ are given with `_hEE`: each $O_E e j$ is open, preconnected, contains the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$; for each $g$ the functions $s \mapsto E_E e j s\,g$ and $s \mapsto N_E e j s\,g$ are analytic on a neighbourhood of $O_E e j$; both are continuous on $O_E e j \times \mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s > 1/2$ one has $E_E e j s\,g = \varphi_E e j s\,g + \sum'_{\xi \in K} \varphi_E e j s(w\,u(\xi)\,g)$ with $w$ the adelic Weyl element and $u$ the unipotent, and $N_E e j s\,g$ equals the Weyl intertwining integral $\int \varphi_E e j s(w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure.
--
--   Two Paley–Wiener packets. For $m = 1,2$ a finite type $\iota_{P m}$, character families $\mu_{P m},\nu_{P m}$ (unitary, trivial on principal ideles, continuous, with $\mu_{P m}(z)\nu_{P m}(z) = \xi_K(z)$ for $z$ in $P.Z$), a swap map $r_{P m}$ exchanging $\mu_{P m}$ and $\nu_{P m}$, separation of distinct indices on the norm-one ideles, section families $\psi_{f m}$ (induced sections for the $\eta$-pair of $(\mu_{P m},\nu_{P m})$, jointly continuous, entire in $s$, archimedean $K$-finite, smooth for the finite-adelic subgroup, uniformly $K$-finite at each infinite place, right $U(N)$-invariant and in the archimedean cut) together with a vertical-strip decay hypothesis `_hψdec`$_m$ (for each index, each $n$, each $\sigma_0$ and each compact $C$ there is an integrable bounded majorant $m(t)$ dominating $(1+|t|)^n\|\psi_{f m} e(\sigma'+it)g\|$ for $|\sigma'| \le \sigma_0$ and $g \in C$) are given. A function $\psi_m$ is a slab profile for $(P.Z,\xi_K)$ — measurable, invariant under left translation by unipotents and by rational Borel points, transforming by $\xi_K$ under the centre, bounded on determinant-norm slabs, and nonvanishing only in a height band — and satisfies the Paley–Wiener representation $\psi_m(g) = \sum_e (4\pi)^{-1}\int_{\mathbb{R}} \psi_{f m} e(\sigma'+it)\,g\,dt$ for every real $\sigma'$ and every $g$. Matching data $(\mathrm{em}_m,\tau_m)$ express $\mu_{P m} i = \mu(\mathrm{em}_m i)\cdot\|\cdot\|^{i\tau_m(i)}$ and $\nu_{P m} i = \nu(\mathrm{em}_m i)\cdot\|\cdot\|^{-i\tau_m(i)}$. Finally a residual projection $p_{\psi m}$ is given, which is an automorphic function for $(P,\xi_K)$, is approximable in $L^2(\Phi_0)$ to within any $\varepsilon>0$ by automorphic elements of the residual span (the span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ with $\chi^2 = \xi_K$ on $P.Z$), and is such that $\int_{\Phi_0}(\theta_{\psi_m}(g) - p_{\psi m}(g))\overline{h(g)} = 0$ for every automorphic $h$ in the residual span, where $\theta_{\psi} := \mathtt{pseudoEisenstein}\,K\,\psi$, $\theta_\psi(g) = \psi(g) + \sum'_{\beta \in K}\psi(w\,u(\beta)\,g)$.
--
--   Conclusion. Under these hypotheses there exist a finite type $\iota_P$, character families $\mu_P,\nu_P : \iota_P \to (\mathbb{A}_K^{\times} \to \mathbb{C}^{\times})$ that are unitary, trivial on principal ideles, continuous (for both $\mu_P$ and $\nu_P$) and satisfy $\mu_P(z)\nu_P(z) = \xi_K(z)$ on $P.Z$, a swap map $r_P$ with $\mu_P(r_P e) = \nu_P e$ and $\nu_P(r_P e) = \mu_P e$, separation of distinct indices on the norm-one ideles, and two section families $\varphi_f,\psi_f$ over the same character family — both induced sections for the $\eta$-pair of $(\mu_P e,\nu_P e)$, both jointly continuous and entire in $s$, with $\psi_f$ archimedean $K$-finite, smooth for the finite-adelic subgroup and uniformly $K$-finite at each infinite place, and with the vertical-strip decay bound above holding for $\varphi_f$ and for $\psi_f$ — together with slab profiles $\varphi,\psi$ for $(P.Z,\xi_K)$ admitting the Paley–Wiener representations $\varphi(g) = \sum_e (4\pi)^{-1}\int_{\mathbb{R}}\varphi_f e(\sigma'+it)g\,dt$ and $\psi(g) = \sum_e (4\pi)^{-1}\int_{\mathbb{R}}\psi_f e(\sigma'+it)g\,dt$ for all $\sigma'$ and $g$, and matching data $(\mathrm{em},\tau)$ with $\mu_P i = \mu(\mathrm{em}\,i)\|\cdot\|^{i\tau(i)}$, $\nu_P i = \nu(\mathrm{em}\,i)\|\cdot\|^{-i\tau(i)}$; and there exist functions $u_{c m},u_{r m},u_{e m}$ for $m=1,2$, all automorphic for $(P,\xi_K)$, such that the constant term $g \mapsto \int h(u(x)g)\,dP.\nu$ of $u_{c m}$ vanishes almost everywhere, $u_{r m}$ is approximable in $L^2(\Phi_0)$ to within any $\varepsilon>0$ by automorphic elements of the residual span, $u_{e m}$ is orthogonal over $\Phi_0$ to every automorphic $h$ whose constant term vanishes almost everywhere or which lies in the residual span, and $\theta_\varphi = u_{c1}+u_{r1}+u_{e1}$, $\theta_\psi = u_{c2}+u_{r2}+u_{e2}$ almost everywhere on $\Phi_0$.
--
--   These data satisfy, in addition: $\varphi = \psi_1$; $\psi = \psi_2$; $u_{e1}$ is right invariant under $\mathtt{principalLevel}\,(𝓞 K)\,K\,N \sqcap \mathtt{finiteAdelicGL2Subgroup}\,K$; $u_{e1}$ lies in the archimedean cut submodule; $u_{e2}$ is right invariant under the same subgroup; $u_{e2}$ lies in the archimedean cut submodule; $u_{e1} = \theta_{\psi_1} - p_{\psi 1}$ almost everywhere on $\Phi_0$; $u_{e2} = \theta_{\psi_2} - p_{\psi 2}$ almost everywhere on $\Phi_0$; for every $e \in \iota_E$ and $j < n_E e$ the coefficient function $t \mapsto \int_{\Phi_0}\theta_\varphi(g)\,\overline{E_E e j(it)(g)}\,dg$ belongs to $L^2(\mathbb{R})$; the family $e \mapsto \int_{\mathbb{R}}\sum_{j} \bigl\|\int_{\Phi_0}\theta_\varphi(g)\overline{E_E e j(it)(g)}\,dg\bigr\|^2\,dt$ is summable over $\iota_E$; and the same two assertions hold with $\theta_\varphi$ replaced by $\theta_\psi$.
--
--   This is the bookkeeping step in the continuous part of the adelic spectral decomposition for $\mathrm{GL}_2$ which re-indexes two separately given Paley–Wiener slab profiles over a single common character family matched into the Eisenstein index family, and simultaneously records, for each of them, a three-way splitting of its pseudo-Eisenstein series into a constant-term-free part, a part approximable by residual functions and a part orthogonal to both, identifying the third summand with the pseudo-Eisenstein series minus its residual projection and asserting square-summability of the Eisenstein coefficient families. It is used by [`AutomorphicForm.exists_forall_tsum_integral_sum_normSq_setIntegral_axis_continuation_sub_le_mul_sq_of_forall_norm_setIntegral_sub_mul_conj_le`](thm.html#AutomorphicForm.exists_forall_tsum_integral_sum_normSq_setIntegral_axis_continuation_sub_le_mul_sq_of_forall_norm_setIntegral_sub_mul_conj_le) and by [`AutomorphicForm.exists_matched_paleyWiener_pair_forall_norm_setIntegral_sub_le_and_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le`](thm.html#AutomorphicForm.exists_matched_paleyWiener_pair_forall_norm_setIntegral_sub_le_and_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_matched_paleyWiener_pair_eq_and_threeWay_of_matched_paleyWiener_of_matched_paleyWiener
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
      (ιP₁ : Type) [Fintype ιP₁]
      (μP₁ νP₁ : ιP₁ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₁ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₁ e)) (_hν₁ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₁ e))
      (_hμic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₁ e)) (_hνic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₁ e))
      (_hμc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₁ e x : ℂˣ) : ℂ))
      (_hμν₁ : ∀ (e : ιP₁)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₁ : ιP₁ → ιP₁) (_hr₁ : ∀ e, μP₁ (rP₁ e) = νP₁ e ∧ νP₁ (rP₁ e) = μP₁ e)
      (_hdist₁ : ∀ e e' : ιP₁, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₁ e x ≠ μP₁ e' x ∨ νP₁ e x ≠ νP₁ e' x)
      (ψf₁ : ιP₁ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₁ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₁ e) αm hαm s) (etaSnd (νP₁ e) αm hαm s) (ψf₁ e s))
      (_hψjc₁ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₁ e p.1 p.2))
      (_hψhol₁ : ∀ e g, Differentiable ℂ (fun s => ψf₁ e s g))
      (_hψK₁ : ∀ e s, IsArchKFinite K (ψf₁ e s)) (_hψsm₁ : ∀ e s, IsKfSmooth K (ψf₁ e s))
      (_hψKu₁ : ∀ (e : ιP₁) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₁ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₁ e x : ℂˣ) : ℂ))
      (_hψdec₁ : ∀ (e : ιP₁) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₁)
      (_hψrep₁ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₁ : ιP₁ → ιE) (τ₁ : ιP₁ → ℝ)
      (_hem₁ : ∀ i : ιP₁, μP₁ i = μ (em₁ i) * NumberField.TateGlobal.normPowChar K (τ₁ i) ∧
        νP₁ i = ν (em₁ i) * (NumberField.TateGlobal.normPowChar K (τ₁ i))⁻¹)
      (_hψlev₁ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₁ i s (g * u) = ψf₁ i s g)
      (_hψty₁ : ∀ i (s : ℂ), ψf₁ i s ∈ archCutSubmodule K tysK)
      (pψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ₁)
      (_hpψc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ₁ g - pψ₁ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (ιP₂ : Type) [Fintype ιP₂]
      (μP₂ νP₂ : ιP₂ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₂ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₂ e)) (_hν₂ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₂ e))
      (_hμic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₂ e)) (_hνic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₂ e))
      (_hμc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₂ e x : ℂˣ) : ℂ))
      (_hμν₂ : ∀ (e : ιP₂)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₂ : ιP₂ → ιP₂) (_hr₂ : ∀ e, μP₂ (rP₂ e) = νP₂ e ∧ νP₂ (rP₂ e) = μP₂ e)
      (_hdist₂ : ∀ e e' : ιP₂, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₂ e x ≠ μP₂ e' x ∨ νP₂ e x ≠ νP₂ e' x)
      (ψf₂ : ιP₂ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₂ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₂ e) αm hαm s) (etaSnd (νP₂ e) αm hαm s) (ψf₂ e s))
      (_hψjc₂ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₂ e p.1 p.2))
      (_hψhol₂ : ∀ e g, Differentiable ℂ (fun s => ψf₂ e s g))
      (_hψK₂ : ∀ e s, IsArchKFinite K (ψf₂ e s)) (_hψsm₂ : ∀ e s, IsKfSmooth K (ψf₂ e s))
      (_hψKu₂ : ∀ (e : ιP₂) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₂ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₂ e x : ℂˣ) : ℂ))
      (_hψdec₂ : ∀ (e : ιP₂) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₂)
      (_hψrep₂ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₂ : ιP₂ → ιE) (τ₂ : ιP₂ → ℝ)
      (_hem₂ : ∀ i : ιP₂, μP₂ i = μ (em₂ i) * NumberField.TateGlobal.normPowChar K (τ₂ i) ∧
        νP₂ i = ν (em₂ i) * (NumberField.TateGlobal.normPowChar K (τ₂ i))⁻¹)
      (_hψlev₂ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₂ i s (g * u) = ψf₂ i s g)
      (_hψty₂ : ∀ i (s : ℂ), ψf₂ i s ∈ archCutSubmodule K tysK)
      (pψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ₂)
      (_hpψc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ₂ g - pψ₂ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0),
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
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK φ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (uc₁ ur₁ ue₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₁) (_huc0₁ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₁ g = 0))
      (_hur₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₁)
      (_hurc₁ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₁ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₁)
      (_hueo₁ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₁ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₁ : AutomorphicForm.pseudoEisenstein K φ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₁ + ur₁ + ue₁)
      (uc₂ ur₂ ue₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_huc₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK uc₂) (_huc0₂ : (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 uc₂ g = 0))
      (_hur₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ur₂)
      (_hurc₂ : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (ur₂ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hue₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue₂)
      (_hueo₂ : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨ h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue₂ g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (_hsum₂ : AutomorphicForm.pseudoEisenstein K ψ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))] uc₂ + ur₂ + ue₂),
    φ = ψ₁ ∧ ψ = ψ₂ ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue₁ (g * u') = ue₁ g) ∧
    ue₁ ∈ archCutSubmodule K tysK ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ue₂ (g * u') = ue₂ g) ∧
    ue₂ ∈ archCutSubmodule K tysK ∧
    ue₁ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ₁ g - pψ₁ g) ∧
    ue₂ =ᵐ[((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))]
      (fun g => AutomorphicForm.pseudoEisenstein K ψ₂ g - pψ₂ g) ∧
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K φ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K φ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) ∧
    (∀ (e : ιE) (j : Fin (nE e)), MemLp (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) 2) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ^ (2 : ℕ)) := by sorry
