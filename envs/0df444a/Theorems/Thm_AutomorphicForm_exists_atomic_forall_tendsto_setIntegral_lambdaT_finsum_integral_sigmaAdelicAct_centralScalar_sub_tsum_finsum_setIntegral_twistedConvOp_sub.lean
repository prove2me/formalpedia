-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
-- name    : AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/02f1ece9-17df-5d2b-97c4-6a954f7b3e86
-- title:
--   Spectral side of the σ-twisted trace formula along Hecke words
-- statement:
--   **Setting.** $K\subseteq L$ is a finite Galois extension of number fields. The datum `D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L` is a Galois descent datum for the adeles: a homomorphism from $\mathrm{Gal}(L/K)$ into the ring automorphisms of $\mathbb{A}_L=$ `AdeleRing (𝓞 L) L`, each automorphism continuous, and compatible with the Galois action on principal adeles. An automorphism $\sigma$ of $L/K$ is fixed, and the hypothesis `hgen` requires every $\tau\in\mathrm{Gal}(L/K)$ to lie in the subgroup of integer powers of $\sigma$, so the Galois group is cyclic with generator $\sigma$. Write $G=\mathrm{GL}_2(\mathbb{A}_L)$ for `AdelicGL2 (𝓞 L) L`, $dg$ for the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` on $G$ (with its Borel structure), $\iota$ for `globalPoints (𝓞 L) L` $: \mathrm{GL}_2(L)\to G$, $z\mapsto z\cdot 1$ for the central embedding `centralScalar (𝓞 L) L` of $\mathbb{A}_L^\times$ into $G$, $\|\cdot\|$ for the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) (the module character of adelic Haar measure), and $\sigma_{\mathbb{A}}(\tau)$ for the entrywise action `sigmaAdelicAct K L D \tau` of $\tau$ on $G$.
--
--   **Slab and fundamental domains.** Real numbers $\alpha<\beta$ with $0<\alpha$ are fixed, together with the determinant slab $\{g\in G:\|\det g\|\in[\alpha,\beta]\}$. The set $\Phi_L\subseteq G$ satisfies `hΦs` (it lies in the slab) and `hΦ` (it is a fundamental domain for the image of $\iota$ acting on the slab, for $dg$ restricted to the slab). A second set $\Phi_0$ satisfies `hΦ₀s` and `hΦ₀` (the same two conditions) and in addition `hΦ₀S`: $\Phi_0$ is contained in the union, over $y$ in a compact set $T_c\subseteq G$, of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂`, consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c\le$ `localHeight` and `xWindowSq` $\le u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$; here $c,u,d_1,d_2$ are real with $0<c$ (`hc`).
--
--   **The centre.** $\mathbb{A}_L^\times$ carries a measurable structure which is the Borel structure of its topology, $\nu_Z$ is a Haar measure on it, and $\Omega_L\subseteq\mathbb{A}_L^\times$ is a fundamental domain for the image of $L^\times$ (under `Units.map` of the structure map) with respect to $\nu_Z$ (`hΩL`).
--
--   **Character, places, levels, types, test factors.** $\xi_L$ is a homomorphism from the full subgroup $\top$ of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$; `hξc` asserts that $z\mapsto\xi_L(z)$ is continuous as a complex-valued function, and `hξt` that $\xi_L$ is trivial on principal ideles. $S_L$ is a finite set of finite places of $L$ which is a union of fibres over the places of $K$: by `hSL`, membership of $w$ in $S_L$ depends only on `HeightOneSpectrum.under (𝓞 K) w`. The ideal $N\subseteq\mathcal{O}_L$ satisfies `hN`: every prime dividing $N$ lies in $S_L$. `tysL : ArchTypeFamily L` assigns to each infinite place of $L$ a finite list of representations of the row isometry subgroup at that place. $S$ is a finite set of finite places of $K$, $\varphi_a$ a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$, one for each finite place $v$ of $K$.
--
--   **Tables.** $X$ is a set of "tables", i.e. of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$, and `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for all $w\in S_L$ and, for every $w\notin S_L$: $(x_w)_2=N(w)\,\xi_L(\det$ `heckeGen (𝓞 L) L w`$)$, where $N(w)=$ `HeckeEigensystem.cNorm w` is the absolute norm of $w$; $\|(x_w)_1\|\le (N(w)+1)\sqrt{\|\xi_L(\det\,\mathrm{heckeGen}\,w)\|}$; and $\overline{(x_w)_1}=\overline{(x_w)_2}\,\|(x_w)_2\|^{-1}(x_w)_1$. The space $C(X,\mathbb{C})$ of continuous complex functions on $X$ is used below.
--
--   **The carrier pins.** Throughout, $P$ denotes `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`: the Borel structure and Haar measure on $G$, the fundamental domain $\Phi_L$, the full central subgroup $\top\le\mathbb{A}_L^\times$, the level subgroups $M\mapsto$ `levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L`, the Hecke generators $w\mapsto$ `heckeGen (𝓞 L) L w`, and on $\mathbb{A}_L$ the Borel structure together with the measure $\nu=P.\nu$ obtained by conditioning additive adelic Haar measure to the box `adelicBox L` (infinite part in the infinite box, finite part integral).
--
--   **The adapted orthonormal system.** $\iota$-indexing is by a type also called $\iota$, with $b:\iota\to(G\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem L ℂ`. The hypotheses are: `hb`, for each $i$ the eigensystem $\mathrm{cls}\,i$ lies in `cuspClasses L P ξL N SL` (level $N$, vanishing $a$- and $b$-entries on $S_L$, non-zero isotypic cusp submodule) and $b_i$ lies in the intersection of `isotypicCuspSubmodule L P ξL N SL (cls i)` (the span of the functions that are smooth cuspidal automorphic at $P$ for $\xi_L$, continuous, right invariant under $P.U\,N$, Hecke eigenfunctions with eigenvalue $a_v$ at each $v\notin S_L$ and central eigenfunctions with eigenvalue $b_v$) with `archCutSubmodule L tysL` (the infimum over infinite places of the supremum of the archimedean type submodules given by `tysL`); `hb₁`, $\int_{\Phi_L}b_i\overline{b_i}\,dg=1$ for every $i$; `hb₀`, $\int_{\Phi_L}b_i\overline{b_j}\,dg=0$ for $i\ne j$; `hbs`, for every cusp class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and the $\mathbb{C}$-span of $b$ over that fibre is exactly the corresponding isotypic cusp submodule cut by `archCutSubmodule L tysL`; and `hbc`, completeness: any $\psi:G\to\mathbb{C}$ which is smooth cuspidal automorphic at $P$ for $\xi_L$, continuous, invariant under right translation by elements of $P.U\,N$, a member of `archCutSubmodule L tysL`, and orthogonal to every $b_i$ over $\Phi_L$, vanishes almost everywhere on $\Phi_L$.
--
--   **Conclusion.** There exist a sequence of tables $\mathrm{tabs}:\mathbb{N}\to(\text{finite places of }L\to\mathbb{C}\times\mathbb{C})$, a proof `htabs` that $\mathrm{tabs}_n\in X$ for every $n$, and a sequence of complex numbers $c:\mathbb{N}\to\mathbb{C}$, such that the following three assertions hold.
--
--   (1) $\sum_n\|c_n\|<\infty$.
--
--   (2) For every $n$ with $c_n\ne0$: first, $\mathrm{tabs}_n$ is constant along fibres outside $S_L$, i.e. $\mathrm{tabs}_n(w)=\mathrm{tabs}_n(w')$ whenever $w,w'\notin S_L$ lie over the same place of $K$; and second, there are an ideal $M\ne0$ of $\mathcal{O}_L$, with `hM` its non-vanishing, and characters $\chi_1,\chi_2:\mathbb{A}_L^\times\to\mathbb{C}^\times$, each continuous as a complex-valued function and trivial on principal ideles, such that for every $w\notin S_L$ the pair $\mathrm{tabs}_n(w)$ equals the pair of $w$-entries of the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), that is $\big(\chi_1(\varpi_w)+\chi_2(\varpi_w),\ \chi_1(\varpi_w)\chi_2(\varpi_w)\big)$ with $\varpi_w$ the uniformiser idele at $w$.
--
--   (3) For every finite set $T$ of finite places of $K$ disjoint from $S$ with $2\le|T|$, such that no place of $L$ above a place of $T$ lies in $S_L$; for every family $\mathrm{ws}$ assigning to each finite place $v$ of $K$ a place $\mathrm{ws}(v)$ of $L$ above $v$; every map $w'$ from finite places of $K$ to finite places of $L$ with $(w'(v))$'s ideal equal to $\sigma^{-1}$ applied to the ideal of $\mathrm{ws}(v)$ for $v\in T$; every family $\varpi$ of elements of the valuation rings of the completions $L_{\mathrm{ws}(v)}$ with $\varpi_v$ irreducible for $v\in T$ and (hypothesis `hϖs0`) with non-zero image in $L_{\mathrm{ws}(v)}$ for $v\in T$; every $\mathrm{ns}:\,$places of $K\to\mathbb{N}$ and every family $r_v:\mathrm{Fin}(\mathrm{ns}(v))\to\mathrm{GL}_2(L_{\mathrm{ws}(v)})$ such that for $v\in T$ the family $r_v$ is a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the integral subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) of $\mathrm{GL}_2(L_{\mathrm{ws}(v)})$ and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $=\mathrm{diag}(\varpi_v,1)$, i.e. the $r_v(i)$ lie in the double coset $U\,\mathrm{diag}(\varpi_v,1)\,U$, their classes modulo $U$ cover that double coset, and $i\mapsto r_v(i)U$ is injective; and every family $z_v\in\mathrm{GL}_2(L_{\mathrm{ws}(v)})$ whose matrix is the scalar $\varpi_v$ times the identity for $v\in T$: there exist continuous $\mathbb{C}$-linear functionals $\mu,\nu_{\mathrm{lin}}:C(X,\mathbb{C})\to\mathbb{C}$ (the latter written $\nu$ in the Lean) with the following two properties.
--
--   (3a) $\mu$ is non-atomic in the $T$-coordinates: for every $\tau$ assigning to each finite place of $K$ an element of $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there is a family $U$ of subsets of $\mathbb{C}\times\mathbb{C}$ with $U(v)$ open and containing $\tau(v)$ for each $v\in T$, such that $\|\mu(g)\|<\varepsilon$ for every $g\in C(X,\mathbb{C})$ which satisfies $\|g\|\le1$ pointwise and vanishes at every $y\in X$ for which $y(w'(v))\notin U(v)$ for some $v\in T$.
--
--   (3b) For all $\mathrm{ks},\mathrm{js}:\,$places of $K\to\mathbb{N}$, every continuous compactly supported $\varphi:G\to\mathbb{C}$, every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (S ∪ T)` holds for $\varphi$, $\varphi_a$, $\varphi_f$ and the semi-local family which at $v\in T$ is the Hecke-word function
--   $$x\ \mapsto\ \sum_{\iota:\mathrm{Fin}(\mathrm{ks}(v))\to\mathrm{Fin}(\mathrm{ns}(v))}\mathbf 1_{\mathrm{semiLocalIntegralSet}}\Big(\big(\mathrm{semiLocalComponent}\,(\mathrm{localEmbed}_{\mathrm{ws}(v)}(r_v(\iota(0))\cdots r_v(\iota(\mathrm{ks}(v)-1))\,z_v^{\mathrm{js}(v)}))\big)^{-1}x\Big)$$
--   (the product being taken in the order of the indices) and at $v\notin T$ is $\varphi_S(v)$ — so that $\varphi_a$ is an archimedean test factor, $\varphi_f$ is locally constant with compact support, each semi-local factor at $v\in S\cup T$ is locally constant with compact support, $\varphi_f(h)$ is the product of the semi-local factors on the components at $S\cup T$ when all components outside $S\cup T$ are integral and is $0$ otherwise, and $\varphi$ is the product of $\varphi_a$ on the archimedean part with $\varphi_f$ on the finite part — and with $\varphi$ bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` and satisfying `IsArchBiFinite L tysL φ` (namely $x\mapsto\varphi(x^{-1})$ lies in `archCutSubmodule L tysL` and $\varphi$ lies in `archDualCutSubmodule L tysL`); and for every $g\in C(X,\mathbb{C})$ given by
--   $$g(x)=\prod_{v\in T}\big(x(w'(v))\big)_1^{\mathrm{ks}(v)}\Big(N(w'(v))^{-1}\big(x(w'(v))\big)_2\Big)^{\mathrm{js}(v)}:$$
--   the function of $R\in\mathbb{R}$ given by
--   $$\int_{\Phi_0}\Big[\lambda^{e^R}\Big(y\mapsto {\sum}^{f}_{q\in\mathrm{GL}_2(L)/Z}\ \int_{\mathbb{A}_L^\times}\xi_L(z)\,\varphi\big(x^{-1}\,\iota(\tilde q)\,\sigma_{\mathbb{A}}(\sigma^{-1})(z\cdot y)\big)\,d\nu_Z(z)\Big)\Big](x)\,dg(x)$$
--   $$-\ \Big(m_Z\sum_{\Psi}\ {\sum}^{f}_{i:\ \mathrm{cls}\,i=\Psi}\int_{\Phi_0}\big(\mathrm{twistedConvOp}\,K\,L\,D\,\sigma\,\varphi\,(b_i)\big)(x)\,\overline{b_i(x)}\,dg(x)\ +\ \big(R\,\nu_{\mathrm{lin}}(g)+\sum_n c_n\,g(\mathrm{tabs}_n)+\mu(g)\big)\Big)$$
--   tends to $0$ as $R\to+\infty$. Here: the inner finsum runs over the quotient of $\mathrm{GL}_2(L)$ by its centre, $\tilde q$ being the chosen representative `q.out`; $z\cdot y$ is `centralScalar (𝓞 L) L z * y`; $\sigma_{\mathbb{A}}(\sigma^{-1})$ is the entrywise action of $\sigma^{-1}$ through $D$; $\lambda^T\psi(x)=\psi(x)-\mathbf 1_{\{H(x)>T\}}\cdot(\mathrm{constantTerm}\,\psi)(x)$ with $H=$ [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean and finite heights) and the constant term taken along the unipotent family [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17) with respect to the adelic measure $P.\nu$ described above, the truncation being applied to the displayed function of $y$ and then evaluated at $y=x$; $m_Z$ is the real number $\nu_Z\big(\Omega_L\cap\{z:\|\det(z\cdot1)\|\in[\alpha,\beta]\}\big)$, regarded as a complex number; $\Psi$ runs (as an unconditional sum over the subtype) through `cuspClasses L P ξL N SL`, the inner finsum over the fibre of $\mathrm{cls}$ above $\Psi$; and `twistedConvOp K L D σ φ (b i)` is the function $x\mapsto\int_G b_i\big(\sigma_{\mathbb{A}}(\sigma)(x h)\big)\varphi(h)\,dh$. All integrals over $\Phi_0$ and $\Phi_L$ are with respect to $dg$.
--
--   This is the spectral side of the $\sigma$-twisted truncated trace formula for $\mathrm{GL}_2$ over $L$ evaluated along Hecke words at the places of $T$, in asymptotic form after the centre has been folded out, with the cuspidal contribution of each Hecke class expressed through the diagonal matrix coefficients of the twisted convolution operator on a complete adapted orthonormal system, and the remaining contributions split into a linear-in-$R$ term, an absolutely convergent atomic sum supported on Eisenstein tables, and a non-atomic remainder. It is used by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_twistedCutTrace_sub), within the comparison of twisted and untwisted traces that produces base change for $\mathrm{GL}_2$ over cyclic extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub.lean

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

theorem AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
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
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
      IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
      Continuous ψ →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
      ψ ∈ archCutSubmodule L tysL →
      (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
      ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0) :
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
                  ∑ᶠ i : {i // cls i = Ψ.1},
                    ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x)
                      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0) := by sorry
