-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/945336cf-e29d-5b36-a59c-c65685a2cb5d
-- title:
--   Spectral side of the truncated centre-folded GL₂ trace formula
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, $\mathcal{O}=\mathcal{O}_K$ its ring of integers, and places are indexed by `HeightOneSpectrum (𝓞 K)` for the finite ones and `InfinitePlace K` for the archimedean ones. `AdelicGL2 (𝓞 K) K` denotes $GL_2(\mathbb{A})$, `globalPoints` the map $GL_2(K)\to GL_2(\mathbb{A})$ induced by $K\to\mathbb{A}$, and `centralScalar` the map $\mathbb{A}^\times\to GL_2(\mathbb{A})$, $z\mapsto \mathrm{diag}(z,z)$.
--
--   The data are grouped as follows.
--
--   *Slab data.* Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$.
--
--   *Siegel covering data.* A set $\Phi_K\subseteq GL_2(\mathbb{A})$, real numbers $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$ and $d_{1K}<d_{2K}$, a finite set $T_K$ of elements of $GL_2(\mathbb{A})$, and the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}\,(\,\cdot\,x)$ of right translates of `centreCutSiegelSet K cK uK d₁K d₂K` covers $GL_2(\mathbb{A})$ modulo $GL_2(K)$ and the centre: for every $g$ there are $\gamma\in GL_2(K)$ and $z\in\mathbb{A}^\times$ with $\gamma g\,\mathrm{diag}(z,z)$ in that union. Here `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component at each infinite place $w$ has local height $\ge c$ and window invariant `xWindowSq` $\le u^2$, and whose archimedean determinant norm at each $w$ lies in $[d_1,d_2]$.
--
--   *Central data.* A measurable space and Borel space structure on $\mathbb{A}^\times$, a Haar measure $\nu_{Z}$ on $\mathbb{A}^\times$, and a set $\Omega_K\subseteq\mathbb{A}^\times$ which, by `hΩK`, is a fundamental domain for the action of the image of $K^\times$ in $\mathbb{A}^\times$ with respect to $\nu_Z$.
--
--   *Character and level data.* A finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the full subgroup $\top\le\mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`) and trivial on the principal ideles (`hξt`); an ideal $N\subseteq\mathcal{O}$ such that every finite place $v$ with $v\mid N$ belongs to $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ a finite list of representations of `rowIsometrySubgroup₀` of the completion at $w$.
--
--   *Test-function data.* A function $f_{a,K}$ on $GL_2(\mathbb{A}_\infty)$ and, for each finite place $v$, a function $f_{S,K}(v)$ on $GL_2(K_v)$, to serve as the archimedean factor and the factors at $S_K$ of the test functions considered below.
--
--   *Table-space data.* A compact set $X$ of functions $x$ from finite places to $\mathbb{C}\times\mathbb{C}$ which, by `hX`, contains every $x$ such that $x_v=0$ for all $v\in S_K$ and, for all $v\notin S_K$, one has $(x_v)_2=\mathrm{N}(v)\,\xi_K(\det \mathrm{heckeGen}_v)$ where $\mathrm{N}(v)=\lvert\mathcal{O}/v\rvert$ (the value `HeckeEigensystem.cNorm v`), $\lVert (x_v)_1\rVert\le(\mathrm{N}(v)+1)\sqrt{\lVert \xi_K(\det \mathrm{heckeGen}_v)\rVert}$, and $\overline{(x_v)_1}=\overline{(x_v)_2}\,\lVert (x_v)_2\rVert^{-1}(x_v)_1$.
--
--   The conclusion asserts the existence of a sequence of tables $t_n\in X$ ($n\in\mathbb{N}$), together with the witnesses $h_{t}$ of membership, and of complex coefficients $c_n$, such that the following three statements hold.
--
--   (i) The series $\sum_n\lVert c_n\rVert$ converges.
--
--   (ii) (Eisenstein nature of the atoms.) For every $n$ with $c_n\ne 0$ there are a nonzero ideal $M\subseteq\mathcal{O}$ and homomorphisms $\chi_1,\chi_2:\mathbb{A}^\times\to\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function, each trivial on the principal ideles, and each unramified at every $v\notin S_K$ in the sense of [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59) (the local character at $v$ is trivial on the units of the valuation ring), such that for every $v\notin S_K$ the pair $t_n(v)$ equals $\bigl(a_v,b_v\bigr)$ for the Hecke eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132) of level $M$, whose entries are $a_v=\chi_1(\varpi_v)+\chi_2(\varpi_v)$ and $b_v=\chi_1(\varpi_v)\chi_2(\varpi_v)$, $\varpi_v$ being the uniformizer idele at $v$.
--
--   (iii) For every finite set $T$ of finite places disjoint from $S_K$ with $\lvert T\rvert\ge 2$, every family $(\varpi_v)_v$ of elements of the valuation rings with $\varpi_v$ irreducible for $v\in T$ and with nonzero image in $K_v$ for $v\in T$ (`hϖKs0`), every family of cardinalities $n_v\in\mathbb{N}$ and of elements $r_v:\mathrm{Fin}(n_v)\to GL_2(K_v)$ such that for $v\in T$ the family $r_v$ is a Hecke coset system for the integral subgroup $\mathrm{im}\,GL_2(\mathcal{O}_v)$ and the element $\mathrm{diag}(\varpi_v,1)$ — that is, each $r_v(i)$ lies in the double coset $U\,\mathrm{diag}(\varpi_v,1)\,U$, every element of that double coset is congruent to some $r_v(i)$ modulo $U$ on the right, and $i\mapsto r_v(i)U$ is injective — and every family $z_v\in GL_2(K_v)$ with $z_v=\varpi_v\cdot 1$ (the scalar matrix) for $v\in T$, there exists a continuous linear functional $\Lambda:C(X,\mathbb{C})\to\mathbb{C}$ with the following two properties.
--
--   First, $\Lambda$ carries no atom in the $T$-coordinates: for every table $\tau$ (an arbitrary function from finite places to $\mathbb{C}\times\mathbb{C}$) and every $\varepsilon>0$ there is a family $U$ of subsets of $\mathbb{C}\times\mathbb{C}$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that every $g\in C(X,\mathbb{C})$ which vanishes at every $y\in X$ admitting some $v\in T$ with $y_v\notin U_v$, and which satisfies $\lVert g(y)\rVert\le 1$ everywhere, satisfies $\lVert\Lambda g\rVert<\varepsilon$.
--
--   Secondly, there exists a further continuous linear functional $s:C(X,\mathbb{C})\to\mathbb{C}$ such that for all families of exponents $k_v,j_v\in\mathbb{N}$, every continuous compactly supported $f:GL_2(\mathbb{A})\to\mathbb{C}$ and every $f_f$ on $GL_2$ of the finite adeles subject to the three conditions:
--
--   — `IsUnitFactorization K (SK ∪ T) f faK ff …`: $f_{a,K}$ is an archimedean test factor (given by a smooth function of the mixed-space entries, with compact support), $f_f$ is locally constant with compact support, the local factors at the places of $S_K\cup T$ are the prescribed ones, namely $f_{S,K}(v)$ for $v\notin T$ and, for $v\in T$, the function $x\mapsto \sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\mathcal{K}_v}\bigl((r_v(\iota(0))\cdots r_v(\iota(k_v-1))\,z_v^{\,j_v})^{-1}x\bigr)$ where $\mathcal{K}_v$ is the set `localIntegralSet K v` of elements of $GL_2(K_v)$ which together with their inverses have entries in $\mathcal{O}_v$; each of these factors at $S_K\cup T$ is a local test function (locally constant, compactly supported); $f_f(h)$ equals the product of the values of these factors at the components of $h$ whenever all components of $h$ outside $S_K\cup T$ lie in $\mathcal{K}_v$, and $f_f(h)=0$ if some component outside $S_K\cup T$ does not; and $f(g)=f_{a,K}(g_\infty)f_f(g_{\mathrm{fin}})$ for all $g$;
--
--   — `IsBiInvariantUnder`: $f$ is invariant under left and under right multiplication by every element of `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the intersection of the principal level subgroup of level $N$ with the kernel of the archimedean projection;
--
--   — `IsArchBiFinite K tysK f`: the function $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule attached to $\mathrm{tys}_K$, and $f$ lies in the corresponding dual cut submodule;
--
--   and for every $g\in C(X,\mathbb{C})$ given on $X$ by the coordinate monomial
--   $$g(x)=\prod_{v\in T}(x_v)_1^{\,k_v}\bigl(\mathrm{N}(v)^{-1}(x_v)_2\bigr)^{j_v},$$
--   the following limit holds as $R\to+\infty$. Write $\mu=$ `adelicGLHaar (Fin 2) (𝓞 K) K` for the Haar measure on $GL_2(\mathbb{A})$ and, for $x\in GL_2(\mathbb{A})$, let $\varphi_x$ be the centre-folded kernel
--   $$\varphi_x(y')=\sum^{\mathrm{f}}_{q\in GL_2(K)/Z(GL_2(K))}\ \int_{\mathbb{A}^\times}\xi_K(z)\,f\bigl(x^{-1}\,\gamma_q\,\mathrm{diag}(z,z)\,y'\bigr)\,d\nu_Z(z),$$
--   where the outer sum is the finite sum (`finsum`) over the quotient of $GL_2(K)$ by its centre and $\gamma_q$ is the image in $GL_2(\mathbb{A})$ of a chosen representative of $q$. Then the function
--   $$R\ \longmapsto\ \int_{\mathcal{F}_{\alpha\beta}}\bigl(\lambda_{e^{R}}\varphi_x\bigr)(x)\,d\mu(x)\ -\ R\cdot s(g)$$
--   tends, as $R\to\infty$, to
--   $$\nu_Z\bigl(\Omega_K\cap\{z:\ \lVert\det\mathrm{diag}(z,z)\rVert_{\mathbb{A}}\in[\alpha,\beta]\}\bigr)\cdot\sum_{\pi}\ \mathrm{cutTrace}(\pi)\ +\ \Bigl(\sum_{n}c_n\,g(t_n)+\Lambda(g)\Bigr).$$
--   Here $\mathcal{F}_{\alpha\beta}=$ `canonicalTruncationDomain K α β` is the canonical truncation domain of the slab; the truncation $\lambda_{e^R}$ is [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48), which subtracts from $\varphi_x$, at points of adelic height $>e^{R}$, the constant term of $\varphi_x$ along the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$ computed with respect to the measure field of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the Borel $\sigma$-algebra on $\mathbb{A}$ and the additive adelic Haar measure conditioned on the adelic box, the height function being [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158). The volume factor is the real number $\nu_Z$ assigns to the intersection of $\Omega_K$ with the set of $z$ whose idele norm of $\det\mathrm{diag}(z,z)$ lies in $[\alpha,\beta]$, viewed in $\mathbb{C}$. The spectral sum runs over the subtype of Hecke eigensystems $\pi$ lying in `cuspClasses K pins' ξK N SK` — those of level exactly $N$ with $a_v=b_v=0$ for all $v\in S_K$ and with nonzero isotypic cuspidal subspace — for the pins $\mathrm{pins}'$ built by `productionPinsOf` from the Siegel union $\bigcup_{x\in T_K}(\,\cdot\,x)$ of right translates of `centreCutSiegelSet K cK uK d₁K d₂K`, the principal levels intersected with `finiteAdelicGL2Subgroup K`, the adelic Hecke generators, and the adelic box; and $\mathrm{cutTrace}(\pi)$ is `cutTrace … π tysK f hf hfc`, the trace of convolution by $f$ on the intersection of the $\pi$-isotypic cuspidal submodule with the archimedean cut submodule of $\mathrm{tys}_K$. As the Lean term is parsed, the volume factor multiplies the spectral sum only, and the atomic contribution $\sum_n c_n g(t_n)+\Lambda(g)$ is added to that product. The atoms $t_n$, the coefficients $c_n$ and properties (i) and (ii) do not depend on $T$, on the Hecke data, on $f$ or on $g$; the functionals $\Lambda$ and $s$ depend on $T$ and the Hecke data but not on the exponents $k_v,j_v$, on $f$ or on $g$.
--
--   This is the spectral side of the Arthur–Selberg trace formula for $GL_2$ over a number field, evaluated along Hecke words at a finite set $T$ of auxiliary places, in the form in which the centre has already been folded out: the truncated kernel integrated over the canonical truncation domain of the determinant slab is asymptotically affine in the truncation parameter $R$, with constant term a volume multiple of the cuspidal trace sum plus an absolutely convergent sum of Eisenstein-table atoms and an atom-free remainder functional. It is used by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul), where the centre-folded kernel is replaced by the adelic kernel paired with the central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul.lean

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

theorem AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_centralScalar_sub_mul
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
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X) :
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
        Filter.Tendsto (fun R : ℝ =>
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              (@AutomorphicForm.lambdaT _
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
                x)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          (R : ℂ) * s g) Filter.atTop (nhds (
          ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N SK π.1 tysK f hf hfc +
          ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g))) := by sorry
