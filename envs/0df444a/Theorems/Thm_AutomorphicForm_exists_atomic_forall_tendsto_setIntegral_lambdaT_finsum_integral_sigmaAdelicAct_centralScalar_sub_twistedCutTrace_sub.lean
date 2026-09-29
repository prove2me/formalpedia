-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6417d80e-c538-5698-9e3d-f43c4ec5eb6e
-- title:
--   Truncated σ-twisted spectral identity along Hecke words
-- statement:
--   Throughout, $L/K$ is a finite Galois extension of number fields, $\mathbb{A}=\mathbb{A}_L$ denotes the adele ring of $L$, and $G=\mathrm{GL}_2(\mathbb{A})$ (`AdelicGL2 (𝓞 L) L`), equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`.
--
--   **Global data and fundamental domains.** Real numbers $\alpha<\beta$ with $0<\alpha$ are fixed, and $\Phi_L\subseteq G$ is a set contained in the determinant slab $\{g:\ \|\det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$ (the idele norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), i.e. the module of the determinant as an idele) which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on that slab, for the Haar measure of $G$ restricted to the slab. On the idele group $\mathbb{A}^{\times}$, carrying a Borel measurable structure, a Haar measure $\nu_{Z_L}$ is fixed together with a set $\Omega_L$ which is a fundamental domain for the subgroup of principal ideles $L^{\times}$.
--
--   **Twisting data.** $D$ is an idele Galois descent datum for $L/K$: a homomorphism from $\mathrm{Gal}(L/K)$ to the continuous ring automorphisms of $\mathbb{A}$ extending the Galois action on principal adeles. An element $\sigma\in\mathrm{Gal}(L/K)$ is fixed, and the hypothesis `hgen` requires every $\tau\in\mathrm{Gal}(L/K)$ to lie in the subgroup of integral powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. The map `sigmaAdelicAct K L D σ.symm` is the entrywise action of $\sigma^{-1}$ on $G$ through $D$.
--
--   **Central character, level, types.** $S_L$ is a finite set of finite places of $L$, and `hSL` requires $S_L$ to be a union of whole fibres over the finite places of $K$. The character $\xi_L$ is a homomorphism from the full subgroup $\top$ of $\mathbb{A}^{\times}$ to $\mathbb{C}^{\times}$; `hξc` asserts continuity of $z\mapsto\xi_L(z)$ and `hξt` its triviality on principal ideles. $N$ is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`), and $\mathrm{tys}_L$ is an archimedean type family for $L$: for each infinite place a finite list of representations of the relevant row-isometry subgroup.
--
--   **Test-function data.** $S$ is a finite set of finite places of $K$, $\varphi_a$ a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by the finite places $v$ of $K$.
--
--   **The space of tables.** $X$ is a set of tables, i.e. of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$, and `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$, while for $w\notin S_L$ one has $(x_w)_2=\mathrm{Nm}(w)\,\xi_L(\det \mathrm{heckeGen}_w)$ with $\mathrm{Nm}(w)$ the absolute norm of $w$ viewed in $\mathbb{C}$ (`HeckeEigensystem.cNorm`), $\|(x_w)_1\|\le(\mathrm{N}w+1)\sqrt{\|\xi_L(\det \mathrm{heckeGen}_w)\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   **The second fundamental domain.** Real numbers $c,u,d_1,d_2$ with $c>0$ are fixed, $T_c\subseteq G$ is compact, and $\Phi_0\subseteq G$ satisfies three conditions: it is covered by the right translates $\mathrm{centreCutSiegelSet}_L(c,u,d_1,d_2)\cdot y$ for $y\in T_c$, where the centre-cut Siegel set consists of those $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose window quantity `xWindowSq` at every infinite place is at most $u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$; it is contained in the determinant slab $[\alpha,\beta]$; and it is a fundamental domain for $\mathrm{GL}_2(L)$ in that slab for the restricted Haar measure.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb{N}\to(\text{finite places of }L\to\mathbb{C}\times\mathbb{C})$ with $\mathrm{tabs}(n)\in X$ for all $n$ (this membership witness being part of the existential), and complex coefficients $c_n$, such that the following three assertions hold.
--
--   First, $\sum_n\|c_n\|$ is summable.
--
--   Second, for every $n$ with $c_n\neq0$: the table $\mathrm{tabs}(n)$ is constant along fibres outside $S_L$, i.e. $\mathrm{tabs}(n)_w=\mathrm{tabs}(n)_{w'}$ whenever $w,w'\notin S_L$ lie over the same finite place of $K$; and there exist a non-zero ideal $M$ of $\mathcal{O}_L$ and two homomorphisms $\chi_1,\chi_2:\mathbb{A}^{\times}\to\mathbb{C}^{\times}$, each continuous as a map into $\mathbb{C}$ and trivial on principal ideles, such that for every $w\notin S_L$ the pair $\mathrm{tabs}(n)_w$ is the pair of Hecke data at $w$ of the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), whose entries at a place are $\chi_1(\varpi)+\chi_2(\varpi)$ and $\chi_1(\varpi)\chi_2(\varpi)$ for the uniformizer idele $\varpi$ at that place.
--
--   Third, for every finite set $T$ of finite places of $K$ which is disjoint from $S$, has at least two elements, and is such that no place of $L$ above a place of $T$ lies in $S_L$, and for every choice of: a place $w_v$ of $L$ above each finite place $v$ of $K$; a map $w'$ from the finite places of $K$ to those of $L$ with $(w' v)$ corresponding to $\sigma^{-1}$ applied to the ideal of $w_v$ for $v\in T$; elements $\varpi_v$ of the valuation ring of the completion $L_{w_v}$ which are irreducible for $v\in T$ and have non-zero image in $L_{w_v}$ there; natural numbers $n_v$ and families $r_{T,v}:\mathrm{Fin}(n_v)\to\mathrm{GL}_2(L_{w_v})$ which, for $v\in T$, form a Hecke coset system (representatives of the left cosets of $\mathrm{GL}_2(\mathcal{O}_{w_v})$ in the double coset of $\mathrm{diag}(\varpi_v,1)$, covering it and pairwise inequivalent) for the integral subgroup and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68); and elements $z_v\in\mathrm{GL}_2(L_{w_v})$ which for $v\in T$ are the scalar matrices $\varpi_v\cdot 1$ — there exist two continuous linear functionals $\mu,\nu:C(X,\mathbb{C})\to\mathbb{C}$ with the following two properties.
--
--   (i) The functional $\mu$ carries no mass concentrated at a point: for every assignment $\tau$ of a pair of complex numbers to each finite place of $K$ and every $\varepsilon>0$ there are sets $U_v$, open and containing $\tau_v$ for $v\in T$, such that $\|\mu(g)\|<\varepsilon$ for every $g\in C(X,\mathbb{C})$ bounded by $1$ in absolute value which vanishes at every table $y\in X$ for which $y_{w'v}\notin U_v$ for some $v\in T$.
--
--   (ii) For all exponent functions $k,j$ from the finite places of $K$ to $\mathbb{N}$, every continuous compactly supported $\varphi:G\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that $\varphi$ admits the semi-local factorisation `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` with local components equal to $\varphi_S$ at $v\notin T$ and, at $v\in T$, to the Hecke-word function
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\mathrm{semiLocalIntegralSet}}\Bigl(\bigl(\mathrm{semiLocalComponent}_v\,\mathrm{localEmbed}_{w_v}\bigl(\textstyle\prod_{m}r_{T,v}(\iota m)\cdot z_v^{\,j_v}\bigr)\bigr)^{-1}x\Bigr),$$
--   and such that $\varphi$ is bi-invariant under $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$ and satisfies `IsArchBiFinite L tysL φ` (that is, $x\mapsto\varphi(x^{-1})$ lies in the archimedean type-cut subspace of $\mathrm{tys}_L$ and $\varphi$ lies in the dual type-cut subspace), and for every $g\in C(X,\mathbb{C})$ given on $X$ by
--   $$g(x)=\prod_{v\in T}\bigl((x_{w'v})_1\bigr)^{k_v}\bigl(\mathrm{Nm}(w'v)^{-1}(x_{w'v})_2\bigr)^{j_v},$$
--   the following difference tends to $0$ as $R\to\infty$ along $\mathbb{R}$:
--   $$\int_{\Phi_0}\Lambda^{e^{R}}\!\Bigl(y\mapsto \sum_{q\in\mathrm{GL}_2(L)/Z}^{\mathrm{finsum}}\ \int_{\mathbb{A}^{\times}}\xi_L(z)\,\varphi\bigl(x^{-1}\,q\,\sigma^{-1}_{\mathbb{A}}(z\cdot y)\bigr)\,d\nu_{Z_L}(z)\Bigr)(x)\,dg(x)\ -\ \mathcal{M}(R),$$
--   where in the integrand the truncation [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) is taken with respect to the data of `productionPinsOf L ΦL (fun M => levelOne N' ⊓ finiteAdelicGL2Subgroup) heckeGen (adelicBox L)`, namely the Borel structure on $\mathbb{A}$ and the additive Haar measure of $\mathbb{A}$ conditioned on the box `adelicBox L`, with the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) and threshold $e^{R}$; thus the function of $y$ displayed above has subtracted from it, on the set where the adelic height exceeds $e^{R}$, its constant term along that unipotent family, and the result is evaluated at $y=x$. The sum over $q$ is a finite-support sum over $\mathrm{GL}_2(L)$ modulo its centre, $q$ being represented through `globalPoints`, and $z\cdot y$ means the product of the central scalar matrix attached to $z$ with $y$.
--
--   The main term $\mathcal{M}(R)$ is
--   $$\nu_{Z_L}\bigl(\Omega_L\cap\{z:\|\det(z\cdot1)\|_{\mathbb{A}}\in[\alpha,\beta]\}\bigr)\cdot\sum_{\Psi}\mathrm{twistedCutTrace}_{K,L,D,\sigma}(\Psi,\varphi)\ +\ \Bigl(R\,\nu(g)+\sum_n c_n\,g(\mathrm{tabs}(n))+\mu(g)\Bigr),$$
--   the volume being taken as a real number and then as a complex number, and $\Psi$ running over the subtype of Hecke eigensystems for $L$ over $\mathbb{C}$ lying in `cuspClasses L pins ξL N SL`, that is those with level exactly $N$, with both Hecke data vanishing at every place of $S_L$, and with non-zero isotypic cusp submodule. For such $\Psi$, $\mathrm{twistedCutTrace}$ is the trace of the $\sigma$-twisted convolution operator attached to $\varphi$ through $D$ on the intersection of the $\Psi$-isotypic cusp submodule with the archimedean type-cut subspace of $\mathrm{tys}_L$ (taken to be $0$ unless that subspace is preserved), and it is evaluated using the continuity and compact support of $\varphi$.
--
--   This is the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, in truncated asymptotic form and with the centre folded out: the truncated centre-folded twisted kernel, integrated over a Siegel-type fundamental domain, is matched as $R\to\infty$ with a cuspidal twisted trace term together with a term linear in $R$, an absolutely convergent atomic sum over Eisenstein tables and a part carrying no point mass. It is used by [`AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_integral_lambdaT_twistedAdelicKernel_sub_twistedCutTrace_sub), where the inner $\xi_L$-average over $\Omega_L$ is replaced by the twisted adelic kernel itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
    Filter.Tendsto (fun R : ℝ =>
      (∫ x in Φ₀,
          @AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
              ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                  AutomorphicForm.sigmaAdelicAct K L D σ.symm
                    (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
            x
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  twistedCutTrace K L D σ
                    (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0) := by sorry
