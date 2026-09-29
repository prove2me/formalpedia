-- Prove2me | Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal
-- name    : AutomorphicForm.exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/4fe37390-1fe4-5c35-882f-ce911b11bd08
-- title:
--   Matched Paley–Wiener approximation of the non-cuspidal non-residual spectrum
-- statement:
--   Throughout, $K$ is a number field, $G$ denotes `AdelicGL2 (𝓞 K) K`, i.e. $\mathrm{GL}_2$ of the adele ring of $K$, and $\mu_G$ denotes the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` for the Borel structure on $G$. Two reals $\alpha,\beta$ are given with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`), and $D$ denotes [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the domain extracted from the canonically chosen truncation datum attached to $(\alpha,\beta)$. The carrier pins $P$ used throughout are `productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`: the Borel $\sigma$-algebra and Haar measure $\mu_G$ on $G$, the domain $D$, the central subgroup $P.Z=\top$ inside the idele units, the level subgroups $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v`, and, on the adeles, the Borel structure together with the additive Haar measure conditioned on the box `adelicBox K`.
--
--   Further ambient data and standing hypotheses. A subset $\Phi_K$ of $G$ is given, carrying no hypothesis. Reals $c_K,u_K,d_{1K},d_{2K}$ are given with $0<c_K$ (`hcK`), $0<d_{1K}$ (`hd₁K`) and $d_{1K}<d_{2K}$ (`hdK`), together with a finite set $T_K\subseteq G$, and the hypothesis `hcovK` asserts `CoversModCentre` for $\bigcup_{x\in T_K}(\cdot\,x)\bigl[\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\,\bigr]$: every $g\in G$ can be moved into this union by multiplying on the left by a rational point of $\mathrm{GL}_2(K)$ and on the right by a central adelic scalar, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose archimedean components have local height at least $c_K$ at every infinite place, satisfy $\mathrm{xWindowSq}\le u_K^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$. A Haar measure $\nu_{Z K}$ on the group of idele units is given, together with a set $\Omega_K$ which by `hΩK` is a fundamental domain (in the sense of `IsFundamentalDomain`) for the image of $K^\times$ in the idele units acting with respect to $\nu_{Z K}$. A finite set $S_K$ of finite places of $K$ is given, and a character $\xi_K:\top\to\mathbb{C}^\times$ on the full group of idele units which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $|\xi_K(z)|=1$ for all $z$ (`hξu`). An ideal $N$ of $\mathcal{O}_K$ is given with `hN`: every finite place $v$ whose prime ideal divides $N$ lies in $S_K$. Finally an archimedean type family $\mathrm{tys}_K$ is given, consisting at each infinite place $w$ of finitely many representations of the row-isometry group; `archCutSubmodule K tysK` is the intersection over infinite places $w$ of the sum over $i$ of the corresponding type submodules of $\{G\to\mathbb{C}\}$.
--
--   The statement then introduces $\alpha_m$, the monoid homomorphism from the idele units to $\mathbb{R}^\times$ obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 K) K)` composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passed to units, and quantifies over the hypothesis $h\alpha_m$ that $\alpha_m(x)>0$ for all $x$; the adeles carry the Borel structure `adeleBorel (𝓞 K) K`.
--
--   Cuspidal data. A type $\iota$, a family $b:\iota\to(G\to\mathbb{C})$ and a family $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` (level, and systems of eigenvalues $a_v$, $b_v$) are given, subject to: `hb`, each $\mathrm{cls}(i)$ lies in `cuspClasses K P ξK N SK` — its level is $N$, $a_v=b_v=0$ for $v\in S_K$, and its isotypic cusp submodule is non-zero — and $b(i)$ lies in `isotypicCuspSubmodule K P ξK N SK (cls i) ⊓ archCutSubmodule K tysK`, the isotypic submodule being the $\mathbb{C}$-span of the functions that are smooth cuspidal automorphic for $P$ and $\xi_K$, continuous, right $U(N)$-invariant, Hecke eigenfunctions with eigenvalue $a_v$ at every $v\notin S_K$ and central eigenfunctions with eigenvalue $b_v$ there; `hbn` and `hbo`, the $b(i)$ are orthonormal for the pairing $\int_D \varphi\,\overline{\psi}\,d\mu_G$; `hbs`, for every $\pi$ in `cuspClasses K P ξK N SK` the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the span of $b$ over it is exactly the $\pi$-isotypic cusp submodule cut by the archimedean types; and `hbc`, completeness: any $\varphi$ which is smooth cuspidal automorphic for $P$ and $\xi_K$, continuous, right $U(N)$-invariant and in the archimedean cut, and orthogonal on $D$ to every $b(i)$, vanishes $\mu_G$-almost everywhere on $D$.
--
--   Eisenstein data. A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\operatorname{Hom}((\mathbb{A}_K^\times),\mathbb{C}^\times)$ are given with hypotheses (named `_hμ`, `_hν`, `_hμic`, `_hνic`, `_hμc`, `_hνc`, `_hμν`, `_hdist`): each $\mu_e,\nu_e$ is unitary, trivial on $K^\times$, continuous, the product $\mu_e\nu_e$ equals $\xi_K$, and distinct indices are separated already on the norm-one ideles [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16). A function $n_E:\iota_E\to\mathbb{N}$ and sections $\varphi_E(e,j,s):G\to\mathbb{C}$ for $j<n_E(e)$, $s\in\mathbb{C}$, are given together with eleven clauses on them: `_hφE`, each $\varphi_E(e,j,s)$ is an induced section for the pair `etaFst (μ e) αm hαm s`, `etaSnd (ν e) αm hαm s`, that is $\varphi(bg)=\mu_e(a)\alpha_m(a)^{s+1/2}\,\nu_e(d)\alpha_m(d)^{-(s+1/2)}\varphi(g)$ for $b$ in the adelic Borel with diagonal entries $a,d$; `_hφEK` and `_hφEf`, archimedean $K$-finiteness and smoothness under the finite-adelic subgroup; `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for fixed $g$; `_hφEKu`, for each $e,j$ and each infinite place $w$ the right translates along `archRowIsometrySubgroup K w` lie in one fixed finite-dimensional space; `_hφEflat`, $\varphi_E(e,j,s)$ agrees with $\varphi_E(e,j,0)$ on the maximal compact subgroup; `_hφElev`, right $U(N)$-invariance; `_hφEty`, membership in the archimedean cut; `_hφEon`, orthonormality of $j\mapsto\varphi_E(e,j,0)$ for the Haar measure `maximalCompactHaar K`; and `_hφEspan`, for every $e$ and every real $t$ each section for the characters at $s=it$ which is continuous, archimedean $K$-finite, right $U(N)$-invariant and in the archimedean cut lies in the span of the $\varphi_E(e,j,it)$. The hypothesis `_hpairs` asserts completeness of the family of character pairs: any unitary pair $(\mu',\nu')$ of idele class characters, continuous with $\mu'\nu'=\xi_K$, which carries a non-zero section on the line $s=it$ with those regularity, level and type properties, agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles. Finally sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E,N_E$ are given, and `_hEE` collects ten clauses: each $O_E(e,j)$ is open, preconnected, and contains both the imaginary axis $\{\operatorname{Re} s=0\}$ and the half-plane $\{\operatorname{Re} s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times G$; and for $\operatorname{Re} s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\bigl(e,j,s,\,w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u$ the unipotent embedding, and $N_E(e,j,s,g)=$ `weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g`, the integral of $\varphi_E(e,j,s)$ over $w^{-1}u(x)g$.
--
--   The vector to be approximated. A function $u_e:G\to\mathbb{C}$ is given with `_hue`, $u_e$ is automorphic for $P$ and $\xi_K$ (membership in the $L^2$-space `LsXiMember` for $\mu_G$, central subgroup $\top$ with character $\xi_K$, and domain $D$), and `_hueo`: for every automorphic $h$ whose constant term $\int h(u(x)g)$, taken against the box-conditioned additive measure, vanishes for almost every $g$, or which lies in [`AutomorphicForm.residualSpan (𝓞 K) K ⊤ ξK`](def/AutomorphicForm_ResidualSpan.html#L12) (the span of the functions $g\mapsto\chi(\det g)$ with $\chi^2=\xi_K$ on $\top$), the integral $\int_D u_e\,\overline{h}\,d\mu_G$ vanishes. A real $\varepsilon>0$ is given.
--
--   Conclusion. There exist a finite type $\iota_P$, families $\mu_P,\nu_P:\iota_P\to\operatorname{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$, a map $r_P:\iota_P\to\iota_P$, a family of sections $\psi_f:\iota_P\to\mathbb{C}\to(G\to\mathbb{C})$, a function $\psi:G\to\mathbb{C}$, maps $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$, and a function $p_\psi:G\to\mathbb{C}$, such that all of the following hold.
--
--   Each $\mu_P(e)$ and $\nu_P(e)$ is unitary and trivial on $K^\times$, both are continuous, and $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for every $z$ in $P.Z$. The map $r_P$ swaps the two characters: $\mu_P(r_P e)=\nu_P(e)$ and $\nu_P(r_P e)=\mu_P(e)$. Distinct indices of $\iota_P$ are separated on the norm-one ideles. For every $e$ and $s$, $\psi_f(e,s)$ is an induced section for `etaFst (μP e) αm hαm s` and `etaSnd (νP e) αm hαm s`; the map $(s,g)\mapsto\psi_f(e,s,g)$ is continuous, $s\mapsto\psi_f(e,s,g)$ is differentiable in $s$ for each $g$, each $\psi_f(e,s)$ is archimedean $K$-finite and smooth for the finite-adelic subgroup, and for each $e$ and each infinite place $w$ the right translates along `archRowIsometrySubgroup K w` lie in one finite-dimensional space. Vertical decay holds in the form `_hψdec`: for every $e$, every $n\in\mathbb{N}$, every $\sigma_0\in\mathbb{R}$ and every compact $C\subseteq G$ there is an integrable, bounded $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_f(e,\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t\in\mathbb{R}$ and all $g\in C$.
--
--   The function $\psi$ is a slab profile, [`AutomorphicForm.IsSlabProfile K ⊤ ξK ψ`](def/AutomorphicForm_SlabProfile.html#L17): it is measurable, invariant under left multiplication by unipotents and by rational Borel points, transforms by $\xi_K$ under the centre, is bounded on every determinant-norm slab $\{g:\|\det g\|\in[d_1,d_2]\}$ with $d_1>0$, and its support is confined to a band $a\le\mathrm{adelicHeight}(g)\le b$ with $a>0$. It is given by the Paley–Wiener representation `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g\in G$,
--   $$\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f\bigl(e,\sigma'+it,g\bigr)\,dt.$$
--   The matching condition `_hem` holds: for every $i\in\iota_P$, $\mu_P(i)=\mu(\mathrm{em}\,i)\cdot$ [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22) and $\nu_P(i)=\nu(\mathrm{em}\,i)\cdot$ `(NumberField.TateGlobal.normPowChar K (τ i))⁻¹`. Moreover each $\psi_f(i,s)$ is right $U(N)$-invariant and lies in `archCutSubmodule K tysK`.
--
--   The function $p_\psi$ is automorphic for $P$ and $\xi_K$; it is approximable by residual functions, in the sense that for every $\varepsilon'>0$ there is an automorphic $r$ in [`AutomorphicForm.residualSpan (𝓞 K) K ⊤ ξK`](def/AutomorphicForm_ResidualSpan.html#L12) with $\|p_\psi-r\|_{L^2(\mu_G\restriction D)}<\varepsilon'$ (measured by `eLpNorm` with exponent $2$); and [`AutomorphicForm.pseudoEisenstein K ψ - p_ψ`](def/AutomorphicForm_SlabProfile.html#L32), where $\mathrm{pseudoEisenstein}(\psi)(g)=\psi(g)+\sum_{\beta\in K}\psi(w\,u(\beta)\,g)$, is orthogonal on $D$ to every automorphic $h$ lying in the residual span.
--
--   Finally, the approximation statement: for every $v:G\to\mathbb{C}$ which is automorphic for $P$ and $\xi_K$, right $U(N)$-invariant, lies in `archCutSubmodule K tysK` and satisfies $\|v\|_{L^2(\mu_G\restriction D)}\le1$,
--   $$\Bigl\|\int_D\bigl(u_e(g)-\bigl(\mathrm{pseudoEisenstein}(\psi)(g)-p_\psi(g)\bigr)\bigr)\,\overline{v(g)}\,d\mu_G(g)\Bigr\|\le\varepsilon.$$
--
--   This is the density step for the continuous part of the spectral decomposition of $\mathrm{GL}_2$ over a number field, in the weak (tested) form: a vector orthogonal to the cuspidal and residual spectra is approximated, against level-$N$ test vectors of the prescribed archimedean types, by a pseudo-Eisenstein series built from a Paley–Wiener slab profile whose characters are matched, up to unramified twists $\|\cdot\|^{i\tau}$, with a fixed separated family of character pairs. It is used by [`AutomorphicForm.exists_matched_paleyWiener_pair_forall_norm_setIntegral_sub_le_and_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le`](thm.html#AutomorphicForm.exists_matched_paleyWiener_pair_forall_norm_setIntegral_sub_le_and_tsum_integral_sum_normSq_sub_setIntegral_axis_continuation_le), where the approximation is combined with the Plancherel identity for the axis continuations of the Eisenstein integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal.lean

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

theorem AutomorphicForm.exists_matched_paleyWiener_forall_norm_setIntegral_sub_pseudoEisenstein_sub_mul_conj_le_of_orthogonal
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
      (ue : AdelicGL2 (𝓞 K) K → ℂ) (_hue : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK ue)
      (_hueo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        ((∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 h g = 0) ∨
          h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ue g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
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
    ∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
      v ∈ archCutSubmodule K tysK →
      eLpNorm v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ 1 →
      ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (ue g - (AutomorphicForm.pseudoEisenstein K ψ g - pψ g)) * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ ε := by sorry
