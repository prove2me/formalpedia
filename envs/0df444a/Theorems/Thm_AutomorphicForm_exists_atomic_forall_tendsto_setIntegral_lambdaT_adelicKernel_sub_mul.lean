-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/863f59b7-a370-56e0-800e-8ea1c0436d0e
-- title:
--   Truncated GL₂ kernel integral along Hecke words: affine asymptotics
-- statement:
--   Fix a number field $K$, with ring of integers $\mathcal O_K$, adele ring $\mathbb A = \mathbb A_K$ and $\mathrm{GL}_2(\mathbb A)$ written `AdelicGL2 (𝓞 K) K`.
--
--   **Slab and covering data.** Reals $\alpha<\beta$ with $0<\alpha$; a set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb A)$; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$; a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb A)$; and the hypothesis `hcovK` that the union $\bigcup_{x\in T_K}(\cdot\,*\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ of right translates of the centre-cut Siegel set (those $g$ whose finite part is integral, whose archimedean components have local height $\ge c_K$, window $\mathrm{xWindowSq}\le u_K^2$ and archimedean determinant norm in $[d_{1K},d_{2K}]$ at every infinite place) covers $\mathrm{GL}_2(\mathbb A)$ modulo $\mathrm{GL}_2(K)$ on the left and the centre on the right, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\cdot I$ in that union.
--
--   **Central data.** A measurable structure on $\mathbb A^\times$ which is the Borel structure, a Haar measure $\nu_{Z,K}$ on $\mathbb A^\times$, and a set $\Omega_K$ which by `hΩK` is a fundamental domain for the action of the group of principal ideles (the range of `Units.map` applied to $K\to\mathbb A$) on $\mathbb A^\times$ with respect to $\nu_{Z,K}$.
--
--   **Spectral data.** A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top\le\mathbb A^\times$ to $\mathbb C^\times$ whose associated function $z\mapsto\xi_K(z)$ is continuous (`hξc`) and trivial on principal ideles (`hξt`); an ideal $N\subseteq\mathcal O_K$ with the hypothesis `hN` that every prime $v$ with $v\mid N$ lies in $S_K$; an archimedean type family $\mathrm{tys}_K$ (a finite list of representations of the row-isometry group at each infinite place); an archimedean test factor $f_{aK}$ on $\mathrm{GL}_2(\mathbb A_\infty)$; and local factors $f_{SK,v}$ on $\mathrm{GL}_2(K_v)$ for each finite $v$.
--
--   **Table space.** A set $X$ of tables $x:\{\text{finite places}\}\to\mathbb C\times\mathbb C$, assumed compact (`hXc`), and containing (`hX`) the set of all tables $x$ such that $x_v=0$ for $v\in S_K$ and, for $v\notin S_K$, writing $\xi_v:=\xi_K(\det(\mathrm{heckeGen}\,v))$: $(x_v)_2 = \mathrm{cNorm}(v)\,\xi_v$ with $\mathrm{cNorm}(v)=\mathrm{N}(v)$ the absolute norm of $v$; $\|(x_v)_1\|\le(\mathrm N(v)+1)\sqrt{\|\xi_v\|}$; and $\overline{(x_v)_1}=\bigl(\overline{(x_v)_2}/\|(x_v)_2\|\bigr)(x_v)_1$.
--
--   **Conclusion.** There exist tables $t_n\in X$ ($n\in\mathbb N$), with the membership witness recorded, and masses $c_n\in\mathbb C$ such that:
--
--   (1) $\sum_n\|c_n\|<\infty$;
--
--   (2) for every $n$ with $c_n\ne 0$ there are a nonzero ideal $M\subseteq\mathcal O_K$ and homomorphisms $\chi_1,\chi_2:\mathbb A^\times\to\mathbb C^\times$, each continuous as a $\mathbb C$-valued function and trivial on principal ideles, which are unramified outside $S_K$ in the sense of [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59) (for $v\notin S_K$ the local character is trivial on units $t$ of $K_v$ with $t,t^{-1}$ integral), and such that for every $v\notin S_K$ the entry $t_n(v)$ equals the pair $(a_v,b_v)$ of the Eisenstein table `eisensteinTableOf K M hM χ₁ χ₂`, that is $a_v=\chi_1(\varpi_v)+\chi_2(\varpi_v)$ and $b_v=\chi_1(\varpi_v)\chi_2(\varpi_v)$ with $\varpi_v$ the uniformiser idele at $v$;
--
--   (3) for every finite set $T$ of finite places disjoint from $S_K$ with $\#T\ge 2$, every family $\varpi_v\in\mathcal O_{K_v}$ with $\varpi_v$ irreducible for $v\in T$ and nonzero image in $K_v$ for $v\in T$, every $n_v\in\mathbb N$ and families $r_v:\mathrm{Fin}(n_v)\to\mathrm{GL}_2(K_v)$ such that for $v\in T$ the $r_v$ form a Hecke coset system for the integral subgroup $\mathrm{GL}_2(\mathcal O_{K_v})$ and the element $\mathrm{diag}(\varpi_v,1)$ (representatives lying in the double coset, covering it modulo the integral subgroup, with distinct cosets), and every family $z_v\in\mathrm{GL}_2(K_v)$ with $z_v=\varpi_v\cdot I$ for $v\in T$, there is a continuous linear functional $\Lambda:C(X,\mathbb C)\to\mathbb C$ with the following two properties.
--
--   First, $\Lambda$ carries no atom along $T$: for every table $\tau$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb C\times\mathbb C$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that $\|\Lambda g\|<\varepsilon$ for every $g\in C(X,\mathbb C)$ bounded by $1$ in absolute value and vanishing at every $y\in X$ for which $y_v\notin U_v$ for some $v\in T$.
--
--   Second, there is a continuous linear functional $s:C(X,\mathbb C)\to\mathbb C$ such that for all exponent families $k_v,j_v\in\mathbb N$, every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb A)$ and every $f_f$ on $\mathrm{GL}_2(\mathbb A_{\mathrm{fin}})$ subject to: `IsUnitFactorization K (SK ∪ T) f faK ff (…)` — $f_{aK}$ is an archimedean test factor, $f_f$ is locally constant with compact support, the local factors at the places of $S_K\cup T$ are locally constant with compact support, $f_f(h)=\prod_{v\in S_K\cup T}f_v(h_v)$ when $h_v$ is integral for all $v\notin S_K\cup T$, $f_f(h)=0$ when some such $h_v$ is non-integral, and $f(g)=f_{aK}(g_\infty)f_f(g_{\mathrm{fin}})$ — where the prescribed local factor at $v\in T$ is the Hecke-word function $x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathrm{localIntegralSet}}\bigl((\prod_m r_v(\iota_m)\cdot z_v^{\,j_v})^{-1}x\bigr)$ and at $v\notin T$ is $f_{SK,v}$; together with bi-invariance of $f$ under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ and `IsArchBiFinite K tysK f` (i.e. $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule of $\mathrm{tys}_K$ and $f$ in the dual cut submodule) — the following holds for every $g\in C(X,\mathbb C)$ given by $g(x)=\prod_{v\in T}(x_v)_1^{k_v}\bigl(\mathrm{cNorm}(v)^{-1}(x_v)_2\bigr)^{j_v}$:
--
--   as $R\to\infty$ the quantity
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta}\ \int_{\Omega_K}\xi_K(z)\,\bigl(\lambda^{e^{R}}K_f(x,\cdot)\bigr)\bigl(z\cdot I\cdot x\bigr)\,d\nu_{Z,K}(z)\ d\mu_{\mathrm{GL}_2}(x)\ -\ R\,s(g)$$
--   converges to
--   $$\nu_{Z,K}\bigl(\Omega_K\cap\{z:\ \|\det(z\cdot I)\|_{\mathbb A}\in[\alpha,\beta]\}\bigr)\cdot\sum_{\pi}\mathrm{cutTrace}(\pi)\ +\ \Bigl(\sum_n c_n\,g(t_n)+\Lambda g\Bigr).$$
--   Here $\mu_{\mathrm{GL}_2}$ is the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A)$ for its Borel structure; the truncation domain is the second set component of the chosen truncation datum for $(\alpha,\beta)$; $K_f(x,y)=\sum_{\gamma\in\mathrm{GL}_2(K)}^{\textstyle\mathrm{finsum}}f(x^{-1}\gamma y)$ is the adelic kernel, evaluated at the diagonal-type point $z\cdot I\cdot x$; $\lambda^{T}\varphi(g)=\varphi(g)-\mathbf 1_{\{\mathrm{adelicHeight}(g)>T\}}(g)\cdot\mathrm{constantTerm}(\varphi)(g)$, the constant term being taken along the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$ against the measure $\nu$ of the carrier pins `productionPinsOf K ΦK (fun M => principalLevel N ⊓ finiteAdelicGL2Subgroup K) heckeGen (adelicBox K)`, namely additive adelic Haar measure conditioned to the adelic box, and the height being [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158); the idele norm is the module `ideleNorm`; and the sum over $\pi$ runs over the subtype of Hecke eigensystems $\Phi:\{\text{finite places}\}\to\mathbb C$ (with level) lying in $\mathrm{cuspClasses}$ for the pins built from the Siegel covering union $\bigcup_{x\in T_K}(\cdot\,*\,x)''\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$, the level subgroups $\mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch})$, the generators $\mathrm{heckeGen}$ and the adelic box, together with $\xi_K$, $N$, $S_K$ — that is, eigensystems of level exactly $N$, with $a_v=b_v=0$ for $v\in S_K$, whose isotypic cusp submodule is nonzero — the summand being $\mathrm{cutTrace}$ of $\pi$, the trace of right convolution by $f$ on the intersection of the $\pi$-isotypic cusp submodule with the archimedean cut submodule of $\mathrm{tys}_K$ (and $0$ if that space is not preserved), the series being a `tsum`.
--
--   This is the spectral side of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field, in the determinant-slab normalisation and tested against Hecke words at two or more auxiliary places: the truncated kernel integral over the canonical truncation domain is asymptotically affine in the truncation parameter $R$, the slope being a continuous functional $s$ on the table space and the intercept splitting into a volume factor times the sum of cuspidal cut traces, an absolutely summable atomic part supported on Eisenstein tables, and an atom-free remainder $\Lambda$. It is used by [`AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder`](thm.html#AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_geometricRemainder), which extracts from it a statement about non-Eisenstein tables carrying no atomic mass.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul.lean

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

theorem
    AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_adelicKernel_sub_mul
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
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y => AutomorphicForm.adelicKernel K f x y)
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
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
