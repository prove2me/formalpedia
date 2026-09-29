-- Prove2me | Theorems.Thm_AutomorphicForm_exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram
-- name    : AutomorphicForm.exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/41b5987e-0441-5ff7-a169-69cce3da367a
-- title:
--   Spectral side of the twisted trace formula along Hecke words
-- statement:
--   Setting. Let $L/K$ be an extension of number fields which is finite and Galois, let $\alpha,\beta$ be real numbers with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`), and write $G=\mathrm{GL}_2(\mathbb{A}_L)$ for `AdelicGL2 (𝓞 L) L`, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`. For an idele $x$, [`NumberField.TateGlobal.ideleNorm L x`](def/NumberField_TateGlobalZeta.html#L19) is the value of the distributive Haar character of $\mathbb{A}_L$ at $x$, and the *determinant slab* is $\mathcal S=\{g\in G:\ \lVert\det g\rVert\in[\alpha,\beta]\}$.
--
--   Global fundamental domains. A set $\Phi_L\subseteq G$ is given which lies in $\mathcal S$ (`hΦs`) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints (𝓞 L) L` (the entrywise map induced by $L\to\mathbb{A}_L$) with respect to the Haar measure of $G$ restricted to $\mathcal S$ (`hΦ`). The idele group $(\mathbb{A}_L)^\times$ carries a Borel measurable structure, $\nu_{Z_L}$ is a Haar measure on it, and $\Omega_L$ is a fundamental domain for the image of $L^\times$ in $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z_L}$ (`hΩL`).
--
--   Galois data. $D$ is an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ which is continuous in each $\tau$ and compatible with the action on $L$ through $L\to\mathbb{A}_L$; and $\sigma\in\mathrm{Gal}(L/K)$ is such that every $\tau$ lies in the subgroup of integer powers of $\sigma$ (`hgen`), so the Galois group is cyclic with generator $\sigma$.
--
--   The excluded places. $S_L$ is a finite set of finite places of $L$ containing every $w$ for which `ramificationIdx'` of the prime under $w$ in $\mathcal{O}_K$ along $w$ differs from $1$ (`hSLram`), and which is a union of whole fibres: $w$ and $w'$ lying over the same place of $K$ belong to $S_L$ together or not at all (`hSL`).
--
--   Central character and level. $\xi_L$ is a homomorphism from the full subgroup $\top\le(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function is continuous (`hξc`) and which is trivial on the image of $L^\times$ (`hξt`). $N$ is an ideal of $\mathcal{O}_L$ such that every finite place $w$ with $w\mid N$ lies in $S_L$ (`hN`). $\mathrm{tys}_L$ is an `ArchTypeFamily L`: for every infinite place $w$ of $L$ a natural number $\mathrm{card}\,w$ and, for each index, a finite-dimensional representation of the row-isometry subgroup at $w$.
--
--   Test-function data. $S$ is a finite set of finite places of $K$, $\varphi_a$ a function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ assigns to each finite place $v$ of $K$ a function on $\mathrm{GL}_2(L\otimes_K K_v)$.
--
--   The table space. $X$ is a set of *tables*, i.e. of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$, and `hX` requires $X$ to contain every table $x$ such that $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, writing $\eta_w=\xi_L\big(\det(\mathrm{heckeGen}\,w)\big)\in\mathbb{C}$ and $\mathrm{cNorm}\,w=\mathrm{N}(w)$ the absolute norm of $w$ viewed in $\mathbb{C}$: $(x_w)_2=\mathrm{cNorm}(w)\,\eta_w$, $\lVert (x_w)_1\rVert\le(\mathrm{N}(w)+1)\sqrt{\lVert\eta_w\rVert}$, and $\overline{(x_w)_1}=\big(\overline{(x_w)_2}/\lVert (x_w)_2\rVert\big)(x_w)_1$.
--
--   The Siegel window. Real numbers $c,u,d_1,d_2$ with $c>0$ (`hc`) are given, together with a compact set $T_c\subseteq G$ and a second set $\Phi_0\subseteq G$ such that: $\Phi_0$ is contained in the union over $y\in T_c$ of the right translates by $y$ of `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (`hΦ₀S`), the set of $g$ whose finite part is integral, whose archimedean local heights are at least $c$ at every infinite place, whose window quantity `xWindowSq` is at most $u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1,d_2]$; $\Phi_0\subseteq\mathcal S$ (`hΦ₀s`); and $\Phi_0$ is again a fundamental domain for the image of $\mathrm{GL}_2(L)$ with respect to the Haar measure of $G$ restricted to $\mathcal S$ (`hΦ₀`).
--
--   Throughout, $\mathcal P$ denotes the carrier data $\mathcal P=$ `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, whose components are: the Borel structure and Haar measure of $G$, the domain $\Phi_L$, the full central subgroup $\top\le(\mathbb{A}_L)^\times$, the level subgroups $M\mapsto$ `levelOne (𝓞 L) L M` intersected with the kernel of the archimedean projection, the Hecke generators $w\mapsto$ `heckeGen (𝓞 L) L w`, the Borel structure on $\mathbb{A}_L$, and the measure $\mathcal P.\nu$ obtained by conditioning the additive Haar measure of $\mathbb{A}_L$ on the box `adelicBox L` (the infinite fundamental box times the integral finite adeles).
--
--   Conclusion. There exist a sequence of tables $\mathrm{tabs}:\mathbb{N}\to(\text{finite places of }L\to\mathbb{C}\times\mathbb{C})$ with $\mathrm{tabs}\,n\in X$ for all $n$ (witnessed by `htabs`), and coefficients $cs:\mathbb{N}\to\mathbb{C}$, such that:
--
--   (1) $\sum_n\lVert cs_n\rVert<\infty$.
--
--   (2) For every $n$ with $cs_n\neq0$: first, $\mathrm{tabs}\,n$ is constant along fibres outside $S_L$, i.e. $\mathrm{tabs}\,n\,w=\mathrm{tabs}\,n\,w'$ whenever $w,w'\notin S_L$ lie over the same place of $K$; and second, there are an ideal $M\neq0$ of $\mathcal{O}_L$ and homomorphisms $\chi_1,\chi_2:(\mathbb{A}_L)^\times\to\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function and trivial on the image of $L^\times$, such that for every $w\notin S_L$ the pair $\mathrm{tabs}\,n\,w$ equals $\big(a_w,b_w\big)$ for the Eisenstein eigensystem [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), whose entries are $a_w=\chi_1(\varpi_w)+\chi_2(\varpi_w)$ and $b_w=\chi_1(\varpi_w)\chi_2(\varpi_w)$ with $\varpi_w$ the uniformiser idele at $w$.
--
--   (3) For every finite set $T$ of finite places of $K$ which is disjoint from $S$, has $\#T\ge2$, and is such that no place $w$ of $L$ above a place of $T$ lies in $S_L$; for every choice of an extension $ws\,v\in v.\mathrm{Extension}(\mathcal{O}_L)$ for each $v$, and of places $w'(v)$ of $L$ with $(w'v).\mathrm{asIdeal}=\sigma^{-1}\cdot (ws\,v).\mathrm{asIdeal}$ for $v\in T$; for every family $\varpi_v$ in the valuation ring of the completion $L_{ws\,v}$ which is irreducible for $v\in T$ and has nonzero image in $L_{ws\,v}$ there (`hϖs0`); for every family of natural numbers $ns$ and every family $rT_v:\mathrm{Fin}(ns\,v)\to\mathrm{GL}_2(L_{ws\,v})$ which, for $v\in T$, is a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the integral subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) of $\mathrm{GL}_2(L_{ws\,v})$ and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $=\mathrm{diag}(\varpi_v,1)$, i.e. the representatives lie in the double coset, cover it modulo the subgroup on the right, and are pairwise distinct modulo it; and for every family $z_v\in\mathrm{GL}_2(L_{ws\,v})$ whose matrix is $\varpi_v$ times the identity for $v\in T$:
--
--   there exist continuous linear functionals $\mu,\nu:C(X,\mathbb{C})\to\mathbb{C}$ such that
--
--   (3a) ($\mu$ carries no atomic mass.) For every $\tau$ assigning to each finite place of $K$ a point of $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that every continuous $g:X\to\mathbb{C}$ which vanishes at every table $y$ admitting some $v\in T$ with $y(w'v)\notin U_v$, and which satisfies $\lVert g\rVert\le1$ pointwise, obeys $\lVert\mu\,g\rVert<\varepsilon$;
--
--   (3b) and for all families of natural numbers $ks,js$, every continuous, compactly supported $\varphi:G\to\mathbb{C}$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ satisfying the three requirements: $\varphi$ is a semi-local factorisation `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` with local data given at $v\in T$ by the Hecke word function
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(ks\,v)\to\mathrm{Fin}(ns\,v)}\mathbf 1_{\text{semi-local integral set at }v}\Big(\big(\text{semi-local component at }v\text{ of the splice of }\textstyle\prod_m rT_v(\iota\,m)\cdot z_v^{\,js\,v}\big)^{-1}x\Big)$$
--   and at $v\notin T$ by $\varphi_S\,v$ (here the splice is [`AdelicDock.localEmbed (𝓞 L) L (ws v).1`](def/AdelicDock_LocalEmbedding.html#L97), and the factorisation condition asserts that $\varphi_a$ is an archimedean test factor, $\varphi_f$ a locally constant compactly supported finite factor, each local datum at $v\in S\cup T$ is locally constant with compact support, $\varphi_f$ equals the product of the local data on elements integral outside $S\cup T$ and vanishes elsewhere, and $\varphi(g)=\varphi_a(\text{arch part})\cdot\varphi_f(\text{finite part})$); $\varphi$ is bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`; and $\varphi$ is arch-bi-finite for $\mathrm{tys}_L$, i.e. $g\mapsto\varphi(g^{-1})$ lies in the archimedean cut submodule and $\varphi$ in the archimedean dual cut submodule attached to $\mathrm{tys}_L$;
--
--   there is $R_0\in\mathbb{R}$ such that for every $R\ge R_0$ and every continuous $g:X\to\mathbb{C}$ given by the Hecke word symbol
--   $$g(x)=\prod_{v\in T}\big((x(w'v))_1\big)^{ks\,v}\big(\mathrm{cNorm}(w'v)^{-1}(x(w'v))_2\big)^{js\,v},$$
--   the following identity holds:
--   $$\int_{\Phi_0}\Big(\int_{\Omega_L}\xi_L(z)\,\big(\Lambda^{e^R}K\big)\big(\mathrm{centralScalar}(z)\cdot x\big)\,d\nu_{Z_L}(z)\Big)\,d\mathrm{Haar}(x) = \nu_{Z_L}\big(\Omega_L\cap\{z:\lVert\det\mathrm{centralScalar}(z)\rVert\in[\alpha,\beta]\}\big)\cdot\!\!\sum_{\Psi}\mathrm{twistedCutTrace}+\big(R\,\nu(g)+\sum_n cs_n\,g(\mathrm{tabs}\,n)+\mu(g)\big),$$
--   where on the left $K$ is the $\sigma$-twisted kernel in the second variable, $K(y)=$ [`AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y`](def/AutomorphicForm_TwistedAdelicKernel.html#L13) $=\sum^{\mathrm f}_{\gamma\in\mathrm{GL}_2(L)}\varphi\big(x^{-1}\gamma\,\sigma^{-1}(y)\big)$ (finite sum over the rational points, the Galois twist acting entrywise through $D$), and $\Lambda^{e^R}$ is the truncation [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) taken with the measure $\mathcal P.\nu$ on $\mathbb{A}_L$, the unipotent family $t\mapsto$ [`AutomorphicForm.unipotentGL2 t`](def/AutomorphicForm_ConstantTerm.html#L17), the height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) (archimedean height times finite height) and threshold $e^R$, i.e. the function minus the indicator of the locus where the height exceeds $e^R$ times its constant term along that family; the volume factor is the real number $\nu_{Z_L}(\cdots)$ coerced to $\mathbb{C}$; and the sum on the right runs over the subtype of Hecke eigensystems $\Psi$ in `cuspClasses L 𝓟 ξL N SL` (those of level exactly $N$ with vanishing $a$ and $b$ at all places of $S_L$ and nonzero isotypic cusp submodule), the summand being `twistedCutTrace K L D σ 𝓟 ξL N SL Ψ tysL φ hφ hφc`, the trace of the $\sigma$-twisted convolution by $\varphi$ on the intersection of the $\Psi$-isotypic cusp submodule with the archimedean cut submodule of $\mathrm{tys}_L$ (taken to be $0$ unless that space is preserved).
--
--   This is the exact form of the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, tested along Hecke words at a set $T$ of at least two auxiliary places of $K$ unramified in $L/K$, with all ramified places absorbed into the excluded set $S_L$: beyond a threshold in the truncation parameter $R$, the truncated twisted kernel integral is an affine function of $R$ whose constant term splits into the cuspidal twisted traces, an absolutely convergent atomic sum over Eisenstein tables, and an atom-free functional of the word symbol. It is used in the comparison of the twisted trace over $L$ with the trace over $K$, feeding [`AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram`](thm.html#AutomorphicForm.exists_continuous_forall_not_isEisenstein_noAtomicMass_twistedGeometricRemainder_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram.lean

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

theorem
    AutomorphicForm.exists_atomic_forall_exists_integral_lambdaT_twistedAdelicKernel_eq_twistedCutTrace_add_symm_unram
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
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSLram : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
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
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) → (
  ∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (@AutomorphicForm.lambdaT _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
        (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ.symm) φ x y)
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
    ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
  (((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
          ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
              Ψ ∈ cuspClasses L
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
            twistedCutTrace K L D σ
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) +
      ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g) := by sorry
