-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/641d358b-f0bc-5202-a78d-9bbd4ae9c0ce
-- title:
--   Eisenstein block of the truncated centre-folded GL₂ kernel
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}$ its adele ring, and $\mathrm{GL}_2(\mathbb{A})$ is written `AdelicGL2 (𝓞 K) K`; tables are functions from the finite places of $K$ (the height-one spectrum of $\mathcal{O}_K$) to $\mathbb{C}\times\mathbb{C}$.
--
--   **Slab and truncation data.** Reals $\alpha<\beta$ with $0<\alpha$; the set [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), namely the second component of the pair of sets chosen by `canonicalTruncationData` for $(\alpha,\beta)$ (the empty set if no truncation datum exists), serves as the fundamental region of integration. A set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb{A})$ is given; it enters only as the `D` field of the carrier pins `productionPinsOf K ΦK …` occurring in the truncation operator, whose `nS` and `ν` fields are the Borel structure on $\mathbb{A}$ and the conditional measure of the adelic additive Haar measure on the box `adelicBox K` (the subset of $\mathbb{A}$ whose infinite component lies in `infiniteBox K` and whose finite component is everywhere integral), and which is otherwise unconstrained.
--
--   **Siegel covering data.** Reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$, a finite set $T_K\subseteq \mathrm{GL}_2(\mathbb{A})$, and the hypothesis `hcovK` that the union of the right translates $(\cdot\, x)$ of `centreCutSiegelSet K cK uK d₁K d₂K` over $x\in T_K$ covers $\mathrm{GL}_2(\mathbb{A})$ modulo the centre: for every $g$ there are $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\, g\, z$ (via `globalPoints` and `centralScalar`) in that union. Here the centre-cut Siegel set consists of the $g$ whose finite part is integral, whose archimedean components all have local height at least $c_K$ and $x$-window square at most $u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K},d_{2K}]$.
--
--   **Central data.** A Haar measure $\nu_{Z_K}$ on the idele units $\mathbb{A}^\times$ (with a Borel measurable structure) and a set $\Omega_K$ which, by `hΩK`, is a fundamental domain for the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_{Z_K}$.
--
--   **Automorphic data.** A finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full subgroup $\top\le \mathbb{A}^\times$ to $\mathbb{C}^\times$ with `hξc` the continuity of $z\mapsto \xi_K(z)$ and `hξt` its triviality on the principal ideles; an ideal $N\subseteq\mathcal{O}_K$ with `hN`: every place $v$ with $v\mid N$ lies in $S_K$; an archimedean type family $\mathrm{tys}_K$ (for each infinite place $w$ a number $\mathrm{card}\,w$ of representations of the local row-isometry group), determining the cut submodule `archCutSubmodule K tysK` $=\bigsqcap_w\bigsqcup_i$ of the corresponding type submodules.
--
--   **Test-function factors.** An archimedean factor $f_{aK}$ on $\mathrm{GL}_2$ of the infinite adeles and local factors $f_{SK}(v)$ on $\mathrm{GL}_2(K_v)$ for each finite place; these occur only in the factorization hypothesis inside the conclusion.
--
--   **The compact set of tables.** A compact set $X$ of tables (`hXc`) which, by `hX`, contains every table $x$ such that $x_v=0$ for all $v\in S_K$ and, for $v\notin S_K$: $(x_v)_2=\mathrm{cNorm}(v)\,\xi_K(\det \mathrm{heckeGen}_v)$ with $\mathrm{cNorm}(v)=\#(\mathcal{O}_K/v)$; $\|(x_v)_1\|\le (\#(\mathcal{O}_K/v)+1)\sqrt{\|\xi_K(\det \mathrm{heckeGen}_v)\|}$; and $\overline{(x_v)_1}=\overline{(x_v)_2}\,\|(x_v)_2\|^{-1}(x_v)_1$.
--
--   **The orthonormal cuspidal family.** A type $\iota$, functions $b_i:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ and eigensystems $\mathrm{cls}(i)\in$ `HeckeEigensystem K ℂ`, subject to five hypotheses, all referring to the pins with $D=$ `canonicalTruncationDomain K α β`, $Z=\top$, $U(M)=$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, $\mathrm{gen}(v)=$ `heckeGen (𝓞 K) K v` and box `adelicBox K`:
--   `hb`: each $\mathrm{cls}(i)$ lies in `cuspClasses … ξK N SK` (level $N$, vanishing $a_v$ and $b_v$ at $v\in S_K$, non-zero isotypic cusp submodule), and $b_i$ lies in `isotypicCuspSubmodule … (cls i)` $\sqcap$ `archCutSubmodule K tysK`, the isotypic submodule being spanned by the continuous, right $U(N)$-invariant smooth cuspidal automorphic functions which are Hecke eigenfunctions with eigenvalue $a_v$ and have central eigenvalue $b_v$ at the places outside $S_K$.
--   `hbn`, `hbo`: the $b_i$ are orthonormal for the pairing $\int_{\text{truncation domain}} b_i\,\overline{b_j}$ against the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K`.
--   `hbs`: for every $\pi$ in `cuspClasses …`, the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ on it equals the cut isotypic submodule of $\pi$.
--   `hbc`: completeness — any $\varphi$ which is a smooth cuspidal automorphic function for these pins and $\xi_K$, is continuous, is right invariant under $U(N)$, lies in `archCutSubmodule K tysK`, and is orthogonal to every $b_i$ over the truncation domain, vanishes almost everywhere for the Haar measure restricted to the truncation domain.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb{N}\to(\text{places}\to\mathbb{C}\times\mathbb{C})$ with $\mathrm{tabs}(n)\in X$ for all $n$, and coefficients $cs:\mathbb{N}\to\mathbb{C}$, such that:
--
--   (1) $\sum_n\|cs(n)\|<\infty$.
--
--   (2) For every $n$ with $cs(n)\neq 0$ there are an ideal $M\neq 0$ and idele class characters $\chi_1,\chi_2:\mathbb{A}^\times\to\mathbb{C}^\times$, each continuous and trivial on the principal ideles, each unramified at every $v\notin S_K$ in the sense of [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59), such that for every $v\notin S_K$ the table value $\mathrm{tabs}(n)_v$ equals the pair $(a_v,b_v)$ of [`LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), i.e. $a_v=\chi_1(\varpi_v)+\chi_2(\varpi_v)$ and $b_v=\chi_1(\varpi_v)\chi_2(\varpi_v)$ for the uniformizer idele $\varpi_v$ at $v$.
--
--   (3) For every finite set $T$ of finite places disjoint from $S_K$ with $\#T\ge 2$, every family $\varpi$ of elements of the local valuation rings which is irreducible at each $v\in T$ and has non-zero image in $K_v$ there, every $n_v\in\mathbb{N}$ and every family $r_v:\mathrm{Fin}(n_v)\to \mathrm{GL}_2(K_v)$ which at each $v\in T$ is a Hecke coset system for the integral subgroup $\mathrm{GL}_2(\mathcal{O}_v)$ and the element $\mathrm{diag}(\varpi_v,1)$ (representatives lying in the double coset, covering it modulo the subgroup on the right, and pairwise distinct in the quotient), and every family $z$ with $z_v=\varpi_v\cdot 1$ as a matrix for $v\in T$, there exists a continuous linear functional $\Lambda$ on $C(X,\mathbb{C})$ with the following two properties.
--
--   (3a) $\Lambda$ is atom-free in the $T$-coordinates: for every table $\tau$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$ with $U_v$ open and $\tau_v\in U_v$ for $v\in T$, such that $\|\Lambda g\|<\varepsilon$ for every $g\in C(X,\mathbb{C})$ bounded by $1$ which vanishes at every $y\in X$ having $y_v\notin U_v$ for some $v\in T$.
--
--   (3b) There exists a further continuous linear functional $s$ on $C(X,\mathbb{C})$ such that for all exponent families $k,j:\text{places}\to\mathbb{N}$, every continuous compactly supported $f:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ and every $f_f$ on $\mathrm{GL}_2$ of the finite adeles such that `IsUnitFactorization K (SK ∪ T) f faK ff` holds with local factors equal to $f_{SK}(v)$ for $v\notin T$ and, for $v\in T$, to
--   $$x\mapsto \sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\text{localIntegralSet}}\Big(\big(\textstyle\prod_m r_v(\iota(m))\cdot z_v^{\,j_v}\big)^{-1}x\Big),$$
--   and such that $f$ is bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and satisfies `IsArchBiFinite K tysK f` (that is, $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in its dual counterpart), the following holds for every $g\in C(X,\mathbb{C})$ given on $X$ by
--   $$g(x)=\prod_{v\in T}(x_v)_1^{\,k_v}\big(\mathrm{cNorm}(v)^{-1}(x_v)_2\big)^{j_v}.$$
--   Write $\mathrm{vol}_Z=\nu_{Z_K}\big(\Omega_K\cap\{z\mid \text{ideleNorm}_K(\det(\text{centralScalar}(z)))\in[\alpha,\beta]\}\big)$ and let $\mathrm{vol}_\Phi$ be the Haar volume of the canonical truncation domain. For $R\in\mathbb{R}$ let $F_R(x)$ denote
--   $$\Lambda^{e^R}\!\big(K^{\mathrm{fold}}_f(x,\cdot)\big)(x)-\Lambda^{e^R}\!\big(K^{\mathrm{cusp}}_f(x,\cdot)\big)(x)-\Lambda^{e^R}\!\big(K^{\mathrm{res}}_f(x,\cdot)\big)(x),$$
--   where $\Lambda^{e^R}$ is [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) for the conditional box measure $\nu$ of the pins, the unipotents $t\mapsto$ `unipotentGL2 t`, the height [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) and threshold $e^R$ — so $\Lambda^{e^R}\varphi(g)=\varphi(g)-\mathbf{1}_{\{e^R<\text{height}\}}(g)\cdot(\text{constant term of }\varphi)(g)$ — applied in the second variable $y'$ and then evaluated at $x$, and where
--   $$K^{\mathrm{fold}}_f(x,y')=\sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(K)/Z}\int \xi_K(z)\,f\big(x^{-1}\,\mathrm{globalPoints}(q)\,(\mathrm{centralScalar}(z)\,y')\big)\,d\nu_{Z_K}(z),$$
--   $$K^{\mathrm{cusp}}_f(x,y')=\mathrm{vol}_Z\sum_{i\in\iota}(\mathrm{convOp}_K f\,b_i)(x)\,\overline{b_i(y')},$$
--   $$K^{\mathrm{res}}_f(x,y')=\frac{\mathrm{vol}_Z}{\mathrm{vol}_\Phi}\sum^{\mathrm{f}}_{\chi}\Big(\int f\,\chi\!\circ\!\det\,d\mu_{\mathrm{Haar}}\Big)\,\chi(\det x)\,\chi^{-1}(\det y'),$$
--   the last finite sum being over those characters $\chi$ of $\mathbb{A}^\times$ with $\chi^2=\xi_K$ on $\top$, trivial on the principal ideles and continuous, and $\mathrm{convOp}_K f\,u$ being the right convolution $g\mapsto\int u(gx)f(x)\,d\mu_{\mathrm{Haar}}(x)$. Then: $F_R$ is integrable on the canonical truncation domain for the adelic Haar measure for all sufficiently large $R$, and
--   $$\Big(\int_{\text{truncation domain}}F_R\,d\mu_{\mathrm{Haar}}\Big)-R\cdot s(g)\ \longrightarrow\ \sum_n cs(n)\,g(\mathrm{tabs}(n))+\Lambda(g)\qquad (R\to\infty).$$
--
--   This is the continuous-spectrum (Eisenstein) block of the spectral side of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field, after folding the centre: the truncated centre-folded kernel with its cuspidal and residual blocks subtracted is shown to be, as the truncation parameter $R$ grows, a linear function of $R$ plus a countable sum of point masses at Eisenstein tables plus an atom-free remainder. It feeds the assembled spectral identity [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul), where the three blocks are recombined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X)
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
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          tabs n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
        (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) f faK ff
          (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else fSK v) →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tysK f →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
        (∀ᶠ R : ℝ in Filter.atTop, IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)))
            (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
        Filter.Tendsto (fun R : ℝ =>
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x))
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          (R : ℂ) * s g) Filter.atTop (nhds ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)) := by sorry
