-- Prove2me | Theorems.Thm_AutomorphicForm_exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
-- name    : AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/90270bac-2e37-5f62-8f17-5b7cea810a37
-- title:
--   Matched Paley–Wiener data realising prescribed smooth coefficient families
-- statement:
--   Throughout, $K$ is a number field and $\alpha,\beta$ are reals with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). Write $\mathbb{A}=\mathrm{AdeleRing}\,(\mathcal{O}_K)\,K$ and $G(\mathbb{A})=\mathrm{GL}_2(\mathbb{A})$. All spaces of automorphic data are taken relative to the carrier pins
--   $$P:=\mathrm{productionPinsOf}\ K\ (\mathtt{canonicalTruncationDomain}\ K\ \alpha\ \beta)\ (M\mapsto \mathtt{principalLevel}\,(\mathcal{O}_K)\,K\,M\sqcap \mathtt{finiteAdelicGL2Subgroup}\,K)\ (v\mapsto \mathtt{heckeGen}\,(\mathcal{O}_K)\,K\,v)\ (\mathtt{adelicBox}\,K),$$
--   that is: the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2)` on $G(\mathbb{A})$, the domain $\Phi_0:=\mathtt{canonicalTruncationDomain}\ K\ \alpha\ \beta$, central subgroup $P.Z=\top$ inside $\mathbb{A}^\times$, the level subgroups $\Gamma(M)\sqcap\ker(\mathtt{glArch})$, the Hecke generators $\mathtt{heckeGen}\,v$, and, on $\mathbb{A}$, the Borel structure together with the additive Haar measure conditioned on the box $\mathtt{adelicBox}\ K$.
--
--   Geometric and measure-theoretic parameters: a set $\Phi_K\subseteq G(\mathbb{A})$, on which no hypothesis is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ and a finite set $T_K\subseteq G(\mathbb{A})$ subject to `hcK` ($0<c_K$), `hd₁K` ($0<d_{1K}$), `hdK` ($d_{1K}<d_{2K}$) and `hcovK`, which asserts $\mathtt{CoversModCentre}$ for $\bigcup_{x\in T_K}(\cdot\,x)''\,\mathtt{centreCutSiegelSet}\ K\ c_K\ u_K\ d_{1K}\ d_{2K}$: every $g\in G(\mathbb{A})$ can be moved into that union by a left translation by a global point of $\mathrm{GL}_2(K)$ and a right central translation by an idele; here the centre-cut Siegel set consists of those $g$ whose finite part is integral, with $\mathtt{localHeight}\ge c_K$ and $\mathtt{xWindowSq}\le u_K^2$ at every infinite place and with $\mathtt{archDetNorm}\in[d_{1K},d_{2K}]$ at every infinite place. Further, $\mathbb{A}^\times$ carries a measurable structure which is Borel, $\nu_{ZK}$ is a Haar measure on $\mathbb{A}^\times$, and $\Omega_K$ is a fundamental domain (`hΩK`) for the range of $K^\times\to\mathbb{A}^\times$ with respect to $\nu_{ZK}$.
--
--   Character and level data: $S_K$ is a finite set of finite places; $\xi_K:\top\to\mathbb{C}^\times$ is a character of the idele group which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary (`hξu`); $N$ is an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); and $\mathrm{tys}_K$ is an `ArchTypeFamily` for $K$, whose associated submodule $\mathtt{archCutSubmodule}\ K\ \mathrm{tys}_K$ is the intersection over infinite places $w$ of the supremum, over the finitely many chosen representations at $w$, of the corresponding type submodules. Finally $\alpha_m:\mathbb{A}^\times\to\mathbb{R}^\times$ is the module character, obtained from $\mathtt{distribHaarChar}\ \mathbb{A}$ by composing with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and passing to units, and $h\alpha_m$ asserts $\alpha_m(x)>0$ for all $x$.
--
--   Under these hypotheses there is a real $C>0$, depending only on the data listed so far, such that the following holds for every choice of the data below.
--
--   Cuspidal basis data: a type $\iota$, functions $b:\iota\to(G(\mathbb{A})\to\mathbb{C})$ and a labelling $\mathrm{cls}:\iota\to\mathrm{HeckeEigensystem}\ K\ \mathbb{C}$, with `hb`: each $\mathrm{cls}\,i$ lies in $\mathtt{cuspClasses}\ K\ P\ \xi_K\ N\ S_K$ (level $N$, vanishing Hecke and central parameters at the places of $S_K$, and non-zero isotypic cusp submodule) and $b\,i$ lies in the intersection of $\mathtt{isotypicCuspSubmodule}\ K\ P\ \xi_K\ N\ S_K\ (\mathrm{cls}\,i)$ — the span of the smooth cuspidal automorphic functions for $\xi_K$ that are continuous, invariant under $P.U\,N$ and Hecke- and centre-eigen outside $S_K$ with the eigenvalues recorded by the eigensystem — with $\mathtt{archCutSubmodule}\ K\ \mathrm{tys}_K$; `hbn`: $\int_{\Phi_0} b\,i\cdot\overline{b\,i}=1$; `hbo`: $\int_{\Phi_0} b\,i\cdot\overline{b\,j}=0$ for $i\ne j$; `hbs`: for each class $\pi$ the fibre $\{i\mid \mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over that fibre is exactly the isotypic cusp submodule of $\pi$ cut by the archimedean types; and `hbc`, the completeness clause: any $\varphi$ that is a smooth cuspidal automorphic function for $\xi_K$, continuous, invariant under $P.U\,N$, of the prescribed archimedean types, and orthogonal over $\Phi_0$ to every $b\,i$, vanishes almost everywhere on $\Phi_0$.
--
--   Eisenstein data: a countable type $\iota_E$ and pairs of idele characters $\mu,\nu:\iota_E\to(\mathbb{A}^\times\to\mathbb{C}^\times)$ subject to `_hμ`, `_hν` (unitary), `_hμic`, `_hνic` (trivial on $K^\times$), `_hμc`, `_hνc` (continuous), `_hμν` ($\mu_e\nu_e=\xi_K$ pointwise) and `_hdist` (distinct indices are separated already on the norm-one ideles, the kernel of $\mathtt{distribHaarChar}$). For each $e$ a multiplicity $n_E(e)\in\mathbb{N}$ and a family $\varphi_{E}(e,j,s)$ of functions on $G(\mathbb{A})$ is given, subject to the hypotheses `_hφE`, `_hφEK`, `_hφEf`, `_hφEjc`, `_hφEhol`, `_hφEKu`, `_hφEflat`, `_hφElev`, `_hφEty`, `_hφEon`, `_hφEspan`, which require respectively: each $\varphi_E(e,j,s)$ is an induced section for the characters $\mathtt{etaFst}\ \mu_e\ \alpha_m\ s=\mu_e\cdot\alpha_m^{\,s+1/2}$ and $\mathtt{etaSnd}\ \nu_e\ \alpha_m\ s=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi(g)$ for $b$ in the adelic Borel subgroup; arch $K$-finiteness (the predicate `RightTranslatesSpanFinite` for right translation by $\mathtt{archRowIsometrySubgroup}\ K\ w$ at every infinite place $w$); smoothness as a vector for the finite adelic subgroup $\ker(\mathtt{glArch})$; joint continuity in $(s,g)$; holomorphy in $s$ for each $g$; at each infinite place a finite-dimensional subspace $W$ containing all the functions $k\mapsto\varphi_E(e,j,s)(gk)$ on $\mathtt{archRowIsometrySubgroup}\ K\ w$; flatness, $\varphi_E(e,j,s)(k)=\varphi_E(e,j,0)(k)$ for $k$ in $\mathtt{adelicMaximalCompact}\ K$; right invariance under $\mathtt{principalLevel}\,N\sqcap\ker(\mathtt{glArch})$; membership in $\mathtt{archCutSubmodule}\ K\ \mathrm{tys}_K$; orthonormality of $j\mapsto\varphi_E(e,j,0)$ on the maximal compact with respect to $\mathtt{maximalCompactHaar}\ K$; and spanning: for every $e$ and every $t\in\mathbb{R}$, every continuous, arch $K$-finite, level-$N$-invariant induced section of the prescribed archimedean types for the characters at $s=it$ lies in the span of the $\varphi_E(e,j,it)$. The clause `_hpairs` is a completeness statement for the family of pairs: for any unitary, idele-class, continuous pair $(\mu',\nu')$ with $\mu'\nu'=\xi_K$, any $t\in\mathbb{R}$ and any non-zero section $\varphi_0$ with the same list of properties at $s=it$, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Axis continuations: sets $O_E(e,j)\subseteq\mathbb{C}$ and families $E_E(e,j,s)$, $N_E(e,j,s)$ of functions on $G(\mathbb{A})$, with `_hEE` requiring (ten clauses, summarised here) that each $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; that $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$ for every $g$, with the two maps $(s,g)\mapsto E_E,N_E$ continuous on $O_E(e,j)\times\mathrm{univ}$; and that for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum'_{\xi\in K}\varphi_E(e,j,s)(w\,u(\xi)\,g)$ with $w=\mathtt{adelicWeyl}$ and $u$ the upper unipotent, and $N_E(e,j,s)(g)=\mathtt{weylIntertwiningIntegral}$ of $\varphi_E(e,j,s)$ at $g$ against the additive adelic Haar measure.
--
--   Coefficient data: a finite set $F\subseteq\iota_E$ and functions $h(e,j):\mathbb{R}\to\mathbb{C}$ with `_hh` (each is $C^\infty$ with compact support) and `_hhF` ($h(e,j)=0$ whenever $e\notin F$).
--
--   The conclusion asserts the existence of: a finite type $\iota_P$; characters $\mu_P,\nu_P:\iota_P\to(\mathbb{A}^\times\to\mathbb{C}^\times)$ that are unitary (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`) and satisfy $\mu_P(e)(z)\nu_P(e)(z)=\xi_K(z)$ for $z\in P.Z$ (`_hμν`); a map $r_P:\iota_P\to\iota_P$ interchanging the two characters, $\mu_P(r_P e)=\nu_P(e)$ and $\nu_P(r_P e)=\mu_P(e)$ (`_hr`); separation of distinct indices on the norm-one ideles (`_hdist`); a family $\psi_f(e,s)$ of functions on $G(\mathbb{A})$ which are induced sections for $\mathtt{etaFst}\ \mu_P(e)\ \alpha_m\ s$ and $\mathtt{etaSnd}\ \nu_P(e)\ \alpha_m\ s$ (`_hψf`), jointly continuous (`_hψjc`), holomorphic in $s$ (`_hψhol`), arch $K$-finite (`_hψK`), smooth for the finite adelic subgroup (`_hψsm`), with finite-dimensional archimedean $K$-types (`_hψKu`), right invariant under $\mathtt{principalLevel}\,N\sqcap\ker(\mathtt{glArch})$ (`_hψlev`), of the prescribed archimedean types (`_hψty`), and satisfying the vertical decay estimate `_hψdec`: for every $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C'\subseteq G(\mathbb{A})$ there is an integrable, bounded above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_f(e,\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$, $g\in C'$; a function $\psi$ on $G(\mathbb{A})$ which is a slab profile for $P.Z$ and $\xi_K$ (`_hψ`: measurable, invariant under left translation by unipotents and by global Borel elements, transforming by $\xi_K$ under the centre, bounded on each determinant-norm slab $[d_1,d_2]$ with $d_1>0$, and supported in a height band) and is represented, for every $\sigma'\in\mathbb{R}$ and every $g$, by $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it)(g)\,dt$ (`_hψrep`); a map $e_m:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu(e_m i)\cdot\mathtt{normPowChar}\,K\,(\tau i)$ and $\nu_P(i)=\nu(e_m i)\cdot(\mathtt{normPowChar}\,K\,(\tau i))^{-1}$ (`_hem`); and finally a function $p_\psi$ which is automorphic for $P$ and $\xi_K$ (`_hpψ`), is approximated in the $L^2$ norm on $\Phi_0$ to arbitrary accuracy by automorphic elements of $\mathtt{residualSpan}$ for $P.Z$ and $\xi_K$, the span of the functions $\chi\circ\det$ with $\chi^2=\xi_K$ on $P.Z$ (`_hpψc`), and is such that $\mathtt{pseudoEisenstein}\ K\ \psi-p_\psi$ is orthogonal over $\Phi_0$ to every automorphic member of that residual span (`_hpψo`).
--
--   For these data the five asserted conjuncts are:
--
--   (i) $e_m$ is injective;
--
--   (ii) every $e\in F$ with $n_E(e)>0$ is of the form $e_m(i)$ for some $i\in\iota_P$;
--
--   (iii) for all $i\in\iota_P$, $t\in\mathbb{R}$ and $j<n_E(e_m i)$,
--   $$\int_{\mathcal{K}}\psi_f(i,it)(k)\,\overline{\varphi_E(e_m i,j,i(t+\tau i))(k)}\,d\,\mathtt{maximalCompactHaar}\,K=\int_{\mathbb{R}}h(e_m i,j)(x)\,e^{\,i(t+\tau i)x}\,dx,$$
--   where $\mathcal{K}=\mathtt{adelicMaximalCompact}\ K$;
--
--   (iv) for every family $\Theta:(e:\iota_E)\to \mathrm{Fin}(n_E e)\to\mathbb{R}\to\mathbb{C}$,
--   $$\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j}\overline{\langle\psi_f(i,it),\varphi_E(e_m i,j,i(t+\tau i))\rangle_{\mathcal{K}}}\;\Theta(e_m i,j)(t+\tau i)\,dt=\sum_{e\in F}\int_{\mathbb{R}}\sum_{j}\overline{\Big(\int_{\mathbb{R}}h(e,j)(x)e^{\,itx}dx\Big)}\;\Theta(e,j)(t)\,dt,$$
--   the inner products being the integrals over $\mathcal{K}$ appearing in (iii);
--
--   (v) the norm control
--   $$\int_{\Phi_0}\big\|\mathtt{pseudoEisenstein}\ K\ \psi\,(g)-p_\psi(g)\big\|^2\,d\,\mathtt{adelicGLHaar}\le C\sum_{e\in F}\sum_{j<n_E(e)}\int_{\mathbb{R}}\Big\|\int_{\mathbb{R}}h(e,j)(x)e^{\,itx}dx\Big\|^2dt,$$
--   where $\mathtt{pseudoEisenstein}\ K\ \psi\,(g)=\psi(g)+\sum'_{\beta\in K}\psi(w\,u(\beta)\,g)$.
--
--   Thus the constant $C$ is uniform: it is chosen before the cuspidal family, the Eisenstein family, the finite set $F$ and the coefficients $h$.
--
--   This is the supply step for the continuous spectrum of $\mathrm{GL}_2$ over a number field: prescribed smooth compactly supported coefficient functions are realised, through their Fourier–Laplace transforms on the unitary axis, by a matched Paley–Wiener datum consisting of a finite packet of induced sections, the associated slab profile $\psi$, its pseudo-Eisenstein series and the residual projection $p_\psi$, together with a uniform bound for the truncated $L^2$ norm of $\theta_\psi-p_\psi$. It is the version recording the values of the one-term coefficients, and is used both for the variant in which only the pairing identity and the norm bound are retained and for the Bessel-type inequality for the coefficients of $\theta_\psi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport.lean

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

open scoped ContDiff

theorem AutomorphicForm.exists_matched_paleyWiener_injective_and_inner_eq_integral_mul_cexp_and_sum_integral_sum_conj_inner_mul_eq_and_setIntegral_normSq_sub_residualProj_le_of_contDiff_hasCompactSupport
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
    ∃ C : ℝ, 0 < C ∧
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
      (F : Finset ιE)
      (h : (e : ιE) → Fin (nE e) → ℝ → ℂ)
      (_hh : ∀ (e : ιE) (j : Fin (nE e)), ContDiff ℝ ∞ (h e j) ∧ HasCompactSupport (h e j))
      (_hhF : ∀ (e : ιE), e ∉ F → ∀ (j : Fin (nE e)), h e j = 0),
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
    Function.Injective em ∧
    (∀ e ∈ F, 0 < nE e → ∃ i : ιP, em i = e) ∧
    (∀ (i : ιP) (t : ℝ) (j : Fin (nE (em i))),
      (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K)) =
        ∫ x : ℝ, h (em i) j x * Complex.exp ((((t + τ i : ℝ) : ℂ)) * Complex.I * (x : ℂ))) ∧
    (∀ (Θ : (e : ιE) → Fin (nE e) → ℝ → ℂ),
      ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          conj (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) * Θ (em i) j (t + τ i)
        = ∑ e ∈ F, ∫ t : ℝ, ∑ j : Fin (nE e), conj (∫ x : ℝ, h e j x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * Θ e j t) ∧
    (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, ‖AutomorphicForm.pseudoEisenstein K ψ g - pψ g‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
        ≤ C * ∑ e ∈ F, ∑ j : Fin (nE e), ∫ t : ℝ, ‖(∫ x : ℝ, h e j x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))‖ ^ 2) := by sorry
