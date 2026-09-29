-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt
-- name    : AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c20dd899-fd62-505d-9274-43dd01e622fc
-- title:
--   Matched unipotent terms: affine in R with atom-free remainder
-- statement:
--   **Setting.** Let $K\subseteq L$ be number fields with $L/K$ finite and Galois, $\alpha,\beta\in\mathbb R$ with $0<\alpha<\beta$. On the $L$-side, $\Phi_L\subseteq \mathrm{GL}_2(\mathbb A_L)$ is contained in the determinant slab $\{g: \|\det g\|_L\in[\alpha,\beta]\}$ (`hΦs`, the idele norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on that slab with the adelic Haar measure `adelicGLHaar` restricted to it (`hΦ`); $\nu_{Z,L}$ is a Haar measure on $(\mathbb A_L)^\times$ and $\Omega_L$ a fundamental domain for the principal ideles $L^\times$ in $(\mathbb A_L)^\times$ (`hΩL`). Further, $D$ is an `IdeleGaloisDescent`, i.e. an action of $\mathrm{Gal}(L/K)$ on $\mathbb A_L$ by continuous ring automorphisms compatible with $L\to\mathbb A_L$; $\sigma:L\simeq_K L$ is such that $\sigma^{-1}$ generates $\mathrm{Gal}(L/K)$ (`hgen`), and $[L:K]$ is prime (`hdeg`).
--
--   **Ramification and level bookkeeping.** Finite sets $S_K$ of primes of $\mathcal O_K$ and $S_L$ of primes of $\mathcal O_L$ satisfy: every $w$ lying over a prime of $S_K$ lies in $S_L$ (`hSL`); $S_L$ is a union of fibres, i.e. $w,w'$ over the same prime of $K$ are simultaneously in or out of $S_L$ (`hSsat`); and every $w$ whose prime below lies outside $S_K$ is unramified, $e(w\mid w\cap\mathcal O_K)=1$ (`hS`). Ideals $N\subseteq\mathcal O_L$ and $N'\subseteq\mathcal O_K$ have all their prime divisors in $S_L$, resp. $S_K$ (`hN`, `hN'`).
--
--   **Characters.** $\xi_L$ is a homomorphism from the full group $(\mathbb A_L)^\times$ (presented as the top subgroup) to $\mathbb C^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`), and satisfies $\xi_L(\det \mathrm{heckeGen}_w)=\xi_L(\det \mathrm{heckeGen}_{w'})$ whenever $w,w'\notin S_L$ lie over the same prime of $K$ (`hξσ`). On the $K$-side, $\Xi$ is a finite set of characters of $(\mathbb A_K)^\times$ and `hΞ` states that $\xi\in\Xi$ holds exactly when $\xi$ is continuous, trivial on principal ideles of $K$, and satisfies $\xi\circ\mathrm{Nm}=\xi_L$, where $\mathrm{Nm}$ is the idelic norm of [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87).
--
--   **Fixed test data and the table space.** $\mathrm{tys}_L$, $\mathrm{tys}_K$ are archimedean type families (for each infinite place a finite list of archimedean representations); $\varphi_a$ is a function on $\mathrm{GL}_2(\mathbb A_{L,\infty})$, $\varphi_S$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$, $f_{a,K}$ a function on $\mathrm{GL}_2(\mathbb A_{K,\infty})$ and $f_{S,K}$ a family of functions on $\mathrm{GL}_2(K_v)$. The set $X$ of tables $x:\{\text{primes of }\mathcal O_L\}\to\mathbb C\times\mathbb C$ is compact (`hXc`) and contains (`hX`) all tables with $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$, $(x_w)_2=\mathrm N(w)\,\xi_L(\det\mathrm{heckeGen}_w)$, $\|(x_w)_1\|\le(\mathrm N(w)+1)\sqrt{\|\xi_L(\det\mathrm{heckeGen}_w)\|}$ and $\overline{(x_w)_1}=\big(\overline{(x_w)_2}/\|(x_w)_2\|\big)(x_w)_1$, where $\mathrm N$ denotes `Ideal.absNorm` (complex-valued via `HeckeEigensystem.cNorm`).
--
--   The $K$-side geometric data mirror the $L$-side: $\Phi_K$ lies in the slab (`hΦKs`) and is a fundamental domain for $\mathrm{GL}_2(K)$ on it (`hΦK`); $\nu_{Z,K}$ is Haar on $(\mathbb A_K)^\times$ and $\Omega_K$ a fundamental domain for the principal ideles of $K$ (`hΩK`).
--
--   **The central–elliptic normalisation `hgeo`.** A constant $c_0\in\mathbb C$ is given such that for every finite $S'\supseteq S_K$ and every pair $(\varphi,f)$ of continuous compactly supported functions on $\mathrm{GL}_2(\mathbb A_L)$, $\mathrm{GL}_2(\mathbb A_K)$ subject to: $\varphi$ is `IsUnitFactorizableAboveOfType` for $\mathrm{tys}_L$, the level $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and $S'$ (so in particular $\varphi$ is archimedean bi-finite of type $\mathrm{tys}_L$); $f$ is `IsUnitFactorizableOfTypeAt` for $\mathrm{tys}_K$, the level $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and $S'$; $\varphi$ and $f$ are matching at $(\sigma^{-1},S')$ in the sense of `AreMatchingAt`; and at each $v\notin S'$ all of whose primes above are unramified, the indicator of the semi-local integral set matches the indicator of the local integral set (`AreMatchingLocal`) — the central and elliptic folds compare by the factor $c_0$:
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\!\!\sum_{\delta}\varphi\big(x^{-1}\delta\,\sigma^{-1}_*(z\cdot x)\big)=c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\big(\mathcal K^{\mathrm{cen}}_f(x,z\cdot x)+\mathcal K^{\mathrm{ell}}_f(x,z\cdot x)\big),$$
--   where $\delta$ runs over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class ([`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766)) equal to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ lying in the elliptic or the central cell, $\sigma^{-1}_*$ is the action `sigmaAdelicAct` of $D$ at $\sigma^{-1}$, $z$ is inserted as the central scalar idele, and $\mathcal K^{\mathrm{cen}},\mathcal K^{\mathrm{ell}}$ are the central and elliptic parts of the adelic kernel, i.e. the finsums of $f(x^{-1}\gamma y)$ over $\gamma$ in the central, resp. elliptic, cell.
--
--   **Conclusion.** For every finite set $T$ of primes of $\mathcal O_K$ disjoint from $S_K$ with $|T|\ge 2$ and such that no prime of $L$ above a $v\in T$ lies in $S_L$, and for every choice of: a prime $w_v$ of $\mathcal O_L$ above each $v$ (`ws`, via `Extension`); a map $w'$ with $(w'_v)=\sigma^{-1}\cdot(w_v)$ as ideals for $v\in T$; uniformizers $\varpi_v$ of the completion of $L$ at $w_v$ (irreducible for $v\in T$, with nonzero image in the completion); numbers $n_v$ and families $r_{T,v}:\mathrm{Fin}\,n_v\to\mathrm{GL}_2(L_{w_v})$ forming a Hecke coset system (`IsHeckeCosetSystem`) for the integral subgroup and the element $\mathrm{diag}(\varpi_v,1)$; central elements $z_v$ equal to the scalar matrix $\varpi_v\cdot 1$ for $v\in T$; and the analogous data $\varpi_{K,v},n_{K,v},r_{K,v},z_{K,v}$ over $K$ at the places $v\in T$ — there exist continuous linear functionals $\Delta_u,\nu_u:C(X,\mathbb C)\to_{L[\mathbb C]}\mathbb C$ (chosen before, hence uniformly in, the Hecke word data below) such that:
--
--   (i) *(no atomic mass for $\Delta_u$)* for every $\tau:\{\text{primes of }\mathcal O_K\}\to\mathbb C\times\mathbb C$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb C\times\mathbb C$ with $U_v$ open and $\tau_v\in U_v$ for all $v\in T$, such that every $g\in C(X,\mathbb C)$ which vanishes at each $y\in X$ for which $y(w'_v)\notin U_v$ for some $v\in T$, and satisfies $\|g(y)\|\le 1$ everywhere, has $\|\Delta_u g\|<\varepsilon$;
--
--   (ii) for all exponent functions $k,j$, every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb A_L)$ and every $\varphi_f$ on $\mathrm{GL}_2(\mathbb A_{L,\mathrm{fin}})$ such that $(\varphi_L,\varphi_a,\varphi_f)$ is a semi-local factorization over $S_K\cup T$ (`IsSemiLocalFactorization`) whose semi-local factor at $v\in T$ is the Hecke word function
--   $$x\mapsto \sum_{\iota:\mathrm{Fin}\,k_v\to\mathrm{Fin}\,n_v}\mathbf 1_{\mathrm{semiLocalIntegralSet}}\Big(\Big(\text{semi-local component of }\big(\textstyle\prod_m r_{T,v}(\iota m)\cdot z_v^{\,j_v}\big)\text{ embedded at }w_v\Big)^{-1}x\Big)$$
--   and is $\varphi_S(v)$ for $v\in S_K\setminus T$, with $\varphi_L$ bi-invariant under $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and archimedean bi-finite of type $\mathrm{tys}_L$; and for every family $\mathrm{fam}$ indexed by the multi-indices $m$ of `SatakeCombination.slotIndex K L ws k j T` (functions assigning to each $v\in T$ an element of $\mathrm{Fin}\,2\to_{\mathrm f}\mathbb N$) such that for each such $m$: $\mathrm{fam}(m)$ is bi-invariant under $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and archimedean bi-finite of type $\mathrm{tys}_K$, $f_{a,K}$ is an archimedean test factor, each $f_{S,K}(v)$ for $v\in S_K$ is a local test function (locally constant with compact support), and there is a finite test factor $f\!f$ (locally constant, compactly supported) which on those $h$ all of whose components outside $S_K\cup T$ are integral equals the product over $v\in S_K\cup T$ of the local factors evaluated at the $v$-component, the factor at $v\in T$ being $x\mapsto\sum_{\iota:\mathrm{Fin}\,(m_v)_0\to\mathrm{Fin}\,n_{K,v}}\mathbf 1_{\mathrm{localIntegralSet}}\big((\prod_m r_{K,v}(\iota m)\cdot z_{K,v}^{(m_v)_1})^{-1}x\big)$ and $f_{S,K}(v)$ otherwise, which vanishes on those $h$ having a non-integral component outside $S_K\cup T$, and with $\mathrm{fam}(m)(g)=f_{a,K}(g_\infty)\,f\!f(g_{\mathrm{fin}})$; and such that $\varphi_L$ and $x\mapsto\sum_m \mathrm{slotFamilyCoeff}(m)\,\mathrm{fam}(m)(x)$ are matching at $(\sigma^{-1},S_K\cup T)$ (`AreMatchingAt`) — there exists $R_0\in\mathbb R$ such that for all $R\ge R_0$ the following four assertions hold.
--
--   Write $\mathcal U_\sigma$ for the set of $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class equal to the class of some $\gamma$ in the unipotent cell of $\mathrm{GL}_2(K)$, and let
--   $$F_L(x,z)=\xi_L(z)\Big(\sum_{\delta\in\mathcal U_\sigma}\varphi_L\big(x^{-1}\delta\,\sigma^{-1}_*(z\cdot x)\big)-\mathbf 1_{\{H_L>e^R\}}(z\cdot x)\,C_L(z\cdot x)\Big),$$
--   where $H_L$ is [`NumberField.AdelicHeight.adelicHeight`](def/NumberField_AdelicHeight.html#L158), and $C_L(g)=\int_{\mathbb A_L}\sum_{\delta}\varphi_L\big(x^{-1}\delta\,\sigma^{-1}_*(u(t)g)\big)\,d\nu(t)$ is the constant term along the unipotent one-parameter subgroup $u(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, the inner finsum being over those $\gamma\in\mathrm{GL}_2(L)$ with $\gamma_{10}=0$ and $N_{L/K}(\gamma_{00}/\gamma_{11})=1$, and $\nu$ the measure of `productionPinsOf L ΦL …`, namely the additive adelic Haar measure of $L$ conditioned to the box `adelicBox L`. Analogously, for $\xi_K\in\Xi$ and a slot index $m$,
--   $$F_K(x,z)=\xi_K(z)\Big(\mathcal K^{\mathrm{uni}}_{\mathrm{fam}(m)}(x,z\cdot x)-\mathbf 1_{\{H_K>e^R\}}(z\cdot x)\,C_K(z\cdot x)\Big),$$
--   with $\mathcal K^{\mathrm{uni}}$ the unipotent part of the adelic kernel (the finsum of $\mathrm{fam}(m)(x^{-1}\gamma y)$ over $\gamma$ in the unipotent cell) and $C_K(g)=\int_{\mathbb A_K}\sum_{\gamma}\mathrm{fam}(m)\big(x^{-1}\gamma\,u(t)g\big)$, the sum over $\gamma\in\mathrm{GL}_2(K)$ with $\gamma_{10}=0$ and $\gamma_{00}/\gamma_{11}=1$, against the corresponding conditioned adelic Haar measure of $K$.
--
--   (a) For every $x$, the function $z\mapsto F_L(x,z)$ is integrable on $\Omega_L$ for $\nu_{Z,L}$.
--
--   (b) The function $x\mapsto\int_{\Omega_L}F_L(x,z)\,d\nu_{Z,L}$ is integrable on `canonicalTruncationDomain L α β` for `adelicGLHaar`.
--
--   (c) For every $\xi_K\in\Xi$ and every slot index $m$: for every $x$ the function $z\mapsto F_K(x,z)$ is integrable on $\Omega_K$ for $\nu_{Z,K}$, and $x\mapsto\int_{\Omega_K}F_K(x,z)\,d\nu_{Z,K}$ is integrable on `canonicalTruncationDomain K α β` for `adelicGLHaar`.
--
--   (d) For every $g\in C(X,\mathbb C)$ which is the monomial $g(x)=\prod_{v\in T}\big(x(w'_v)\big)_1^{k_v}\big(\mathrm N(w'_v)^{-1}(x(w'_v))_2\big)^{j_v}$ on $X$,
--   $$\int_{\Phi_0^L}\!\int_{\Omega_L}F_L-c_0\sum_{\xi_K\in\Xi}\ \sum_{m}\mathrm{slotFamilyCoeff}(m)\int_{\Phi_0^K}\!\int_{\Omega_K}F_K=R\cdot\nu_u g+\Delta_u g,$$
--   where $\Phi_0^L$, $\Phi_0^K$ are the canonical truncation domains of $L$ and $K$ for $(\alpha,\beta)$, the outer integrals are taken against the adelic Haar measures, the inner ones against $\nu_{Z,L}$, $\nu_{Z,K}$, and $m$ runs over `SatakeCombination.slotIndex K L ws k j T`.
--
--   Thus the difference of the truncated unipotent contributions of the $\sigma^{-1}$-twisted side and the $c_0$-weighted Satake combination of the untwisted sides is an affine function of the truncation parameter $R$, with slope $\nu_u g$ and intercept $\Delta_u g$ given by functionals of the Hecke monomial $g$ that do not depend on $R$, on the exponents $k,j$ or on the test functions, and whose intercept functional $\Delta_u$ carries no atomic mass in the sense of (i).
--
--   This is the unipotent (parabolic) step in the comparison of the truncated twisted and untwisted adelic trace formulas for $\mathrm{GL}_2$ along a cyclic extension of prime degree, in the style of Langlands' base change for $\mathrm{GL}(2)$: the truncated unipotent terms of matched test functions differ by a term affine in the truncation parameter whose constant part is an atom-free functional of the Hecke monomial. It is used in [`AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform`](thm.html#AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform), where the $R$-linear parts are compared and eliminated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt
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
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hSsat : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
        ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ =
          ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w'), Subgroup.mem_top _⟩)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (c₀ : ℂ)
    (hgeo :
      ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' →
      ∀ (φ : AdelicGL2 (𝓞 L) L → ℂ) (_hφ : Continuous φ) (_hφc : HasCompactSupport φ)
        (_hφt : AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
        (_hft : AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f)
        (_hm : AutomorphicForm.AreMatchingAt K L σ.symm S' φ f)
        (_hunit : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))),
        (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) =
                  ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        c₀ * ∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
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
      ∃ Δu νu : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δu g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL →
        IsArchBiFinite L tysL φL →
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)
        ) →
      AreMatchingAt K L σ.symm (SK ∪ T) φL
        (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →

      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
      (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ) = ConjClasses.mk γ},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
        c₀ * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (R : ℂ) * νu g + Δu g := by sorry
