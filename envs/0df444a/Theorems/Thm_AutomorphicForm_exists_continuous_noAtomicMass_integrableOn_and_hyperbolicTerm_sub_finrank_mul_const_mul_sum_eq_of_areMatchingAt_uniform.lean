-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform
-- name    : AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/52ab40e4-7cab-55ef-8a0e-fc9ba759090a
-- title:
--   Truncated hyperbolic terms compared with a uniform slope λ
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ a finite Galois extension, $\alpha,\beta$ are reals with $0<\alpha<\beta$, and the degree $\ell=\operatorname{finrank}_K L$ is prime (`hdeg`). A generator is fixed in the sense that $\sigma:L\simeq_K L$ satisfies `hgen`: every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma^{-1}$. Further, $D$ is an `IdeleGaloisDescent` datum for $\mathcal O_L$ over $K,L$, that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$ which is continuous in each $\tau$ and compatible with $\operatorname{algebraMap}$ from $L$; `sigmaAdelicAct K L D σ.symm` is the induced automorphism of $\mathrm{GL}_2(\mathbb A_L)$ at $\sigma^{-1}$.
--
--   *Geometric and measure-theoretic data.* On the $L$ side: $\Phi_L\subseteq\mathrm{GL}_2(\mathbb A_L)$ is contained in the determinant slab $\{g:\ \|\det g\|_L\in[\alpha,\beta]\}$ (`hΦs`, with $\|\cdot\|_L$ the `TateGlobal.ideleNorm`) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that slab (`hΦ`); $\nu_{Z,L}$ is a Haar measure on $\mathbb A_L^\times$ (for a measurable and Borel structure on the ideles) and $\Omega_L$ is a fundamental domain for the principal ideles $L^\times$ in $\mathbb A_L^\times$ with respect to $\nu_{Z,L}$ (`hΩL`). On the $K$ side the hypotheses `hΦKs`, `hΦK`, together with $\nu_{Z,K}$ and `hΩK`, are the exact analogues for $\Phi_K$, $\nu_{Z,K}$, $\Omega_K$.
--
--   *Places, level and character data.* $S_K$ is a finite set of primes of $\mathcal O_K$ and $S_L$ one of primes of $\mathcal O_L$, subject to: `hSL`, every $w$ lying under a prime of $S_K$ belongs to $S_L$; `hSsat`, $S_L$ is a union of fibres, i.e. $w\in S_L\iff w'\in S_L$ whenever $w,w'$ lie over the same prime of $\mathcal O_K$; `hS`, every $w$ whose prime below lies outside $S_K$ has ramification index `Ideal.ramificationIdx'` equal to $1$. The character $\xi_L$ is a homomorphism from the full subgroup of $\mathbb A_L^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`), and satisfies `hξσ`: $\xi_L(\det\,\mathtt{heckeGen}\,w)=\xi_L(\det\,\mathtt{heckeGen}\,w')$ for all $w,w'\notin S_L$ lying over the same prime of $K$. The ideal $N\subseteq\mathcal O_L$ has all its prime divisors in $S_L$ (`hN`), the ideal $N'\subseteq\mathcal O_K$ has all its prime divisors in $S_K$ (`hN'`), and $\mathrm{tys}_L$, $\mathrm{tys}_K$ are archimedean type families (a number of archimedean representations at each infinite place). Fixed test factors are $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, a family $\varphi_S$ of functions on $\mathrm{GL}_2(L\otimes_K K_v)$, $f_{a,K}$ on $\mathrm{GL}_2$ of the infinite adeles of $K$, and a family $f_{S,K}$ of functions on $\mathrm{GL}_2(K_v)$. The finite set $\Xi$ consists of homomorphisms $\xi_K$ from the full subgroup of $\mathbb A_K^\times$ to $\mathbb C^\times$, and `hΞ` characterises it: $\xi_K\in\Xi$ if and only if $\xi_K$ is continuous, trivial on the principal ideles of $K$, and $\xi_K$ composed with the idelic norm of the `genuineBaseChange` base-change datum equals $\xi_L$.
--
--   *The table space.* $X$ is a compact set of functions from the primes of $\mathcal O_L$ to $\mathbb C\times\mathbb C$ (`hXc`), and `hX` requires that $X$ contain every $x$ with $x_w=0$ for $w\in S_L$ and, for $w\notin S_L$: $(x_w)_2=\mathcal N(w)\,\xi_L(\det\,\mathtt{heckeGen}\,w)$ with $\mathcal N(w)=$ `HeckeEigensystem.cNorm w` the absolute norm of $w$, $\|(x_w)_1\|\le(\mathcal N(w)+1)\sqrt{\|\xi_L(\det\,\mathtt{heckeGen}\,w)\|}$, and $\overline{(x_w)_1}=\bigl(\overline{(x_w)_2}/\|(x_w)_2\|\bigr)(x_w)_1$.
--
--   *The central–elliptic input.* A complex constant $c_0$ is given, together with the hypothesis `hgeo`: for every finite $S'\supseteq S_K$, every continuous compactly supported $\varphi$ on $\mathrm{GL}_2(\mathbb A_L)$ which is `IsUnitFactorizableAboveOfType` for $K,L,\mathrm{tys}_L$ at level $\mathtt{levelOne}(N)\sqcap\mathtt{finiteAdelicGL2Subgroup}\,L$ over $S'$ (so in particular archimedean bi-finite of type $\mathrm{tys}_L$), every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb A_K)$ which is `IsUnitFactorizableOfTypeAt` for $\mathrm{tys}_K$ at level $\mathtt{principalLevel}(N')\sqcap\mathtt{finiteAdelicGL2Subgroup}\,K$ over $S'$, such that $\varphi$ and $f$ are matching at $\sigma^{-1}$ over $S'$ (existence of archimedean, finite and semi-local factorisations with matching archimedean factors and matching local factors at each $v\in S'$) and such that at every $v\notin S'$ all of whose primes above are unramified the indicator functions of the semi-local and local integral sets are locally matching, one has
--   $$\int_{\Phi_L}\!\int_{\Omega_L}\xi_L(z)\!\!\sum_{\delta}^{\mathrm f}\varphi\bigl(x^{-1}\delta\,\sigma^{-1}(z\,x)\bigr)\,d\nu_{Z,L}\,d\mu_L = c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\!\int_{\Omega_K}\xi_K(z)\bigl(\mathcal K^{\mathrm{cen}}_f(x,z x)+\mathcal K^{\mathrm{ell}}_f(x,z x)\bigr)d\nu_{Z,K}\,d\mu_K,$$
--   where the finsum runs over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class is carried by `normClassMap hgen` to the conjugacy class of some $\gamma$ in the elliptic or the central cell, $z$ is inserted through `centralScalar`, $\delta$ through `globalPoints`, and $\mathcal K^{\mathrm{cen}}_f,\mathcal K^{\mathrm{ell}}_f$ are `adelicKernelCentralPart` and `adelicKernelEllipticPart`, the finsums of $f(x^{-1}\gamma y)$ over the central and elliptic cells.
--
--   *Conclusion.* There exists $\lambda\in\mathbb C$ with $\lambda\ne0$ such that the following two assertions hold.
--
--   (1) *Normalisation of $\lambda$.* If there exist a finite $S'\supseteq S_K$ and functions $\varphi,f$ with all the properties listed in `hgeo` (continuity, compact support, factorisability of the stated type and level on each side, matching at $\sigma^{-1}$ over $S'$, and local matching of the integral-set indicators at every $v\notin S'$ unramified in $L$) for which the $K$-side central–elliptic expression $\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(\mathcal K^{\mathrm{cen}}_f(x,zx)+\mathcal K^{\mathrm{ell}}_f(x,zx)\bigr)$ is non-zero, then $\ell\,\lambda=c_0$ in $\mathbb C$.
--
--   (2) *Hyperbolic comparison along Hecke words.* For every finite set $T$ of primes of $\mathcal O_K$ with $T$ disjoint from $S_K$, $|T|\ge2$, and every prime of $L$ above a member of $T$ lying outside $S_L$; for every choice of an extension $ws_v$ of each $v$ to $\mathcal O_L$ and a map $w'$ on primes of $K$ with $(w'_v)=\sigma^{-1}\cdot (ws_v)$ as ideals for $v\in T$; for every family $\varpi_v$ in the valuation ring at $ws_v$ which is irreducible for $v\in T$ and has non-zero image in the completion (the latter recorded as `hϖs0`), every $ns$ and every family $rT_v:\mathrm{Fin}(ns_v)\to\mathrm{GL}_2$ of the completion at $ws_v$ which for $v\in T$ is an `IsHeckeCosetSystem` for the integral subgroup and the element $\mathrm{diag}(\varpi_v,1)$ (representatives of the double coset, covering it modulo the subgroup on the right, with injective induced map to the quotient), and every $zs_v$ which for $v\in T$ is the scalar matrix $\varpi_v\cdot 1$; and, on the $K$ side, for every family $\varpi_{K,v}$ in the valuation ring at $v$ irreducible for $v\in T$ with non-zero image (`hϖKs0`), every $nK$ and Hecke coset systems $rK_v$ for the integral subgroup and $\mathrm{diag}(\varpi_{K,v},1)$, and every $zK_v$ equal for $v\in T$ to the scalar matrix $\varpi_{K,v}\cdot1$ — there exist continuous linear functionals $\Delta_h,\nu_h:C(X,\mathbb C)\to_L\mathbb C$ with the following two properties.
--
--   First, $\Delta_h$ carries no atomic mass in the coordinates indexed by $T$: for every $\tau$ from the primes of $K$ to $\mathbb C\times\mathbb C$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb C\times\mathbb C$ with $U_v$ open and $\tau_v\in U_v$ for $v\in T$, such that $\|\Delta_h g\|<\varepsilon$ for every $g\in C(X,\mathbb C)$ bounded by $1$ in absolute value which vanishes at every $y\in X$ having $y_{w'_v}\notin U_v$ for some $v\in T$.
--
--   Secondly, for all $ks,js$ from primes of $K$ to $\mathbb N$, every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb A_L)$ and every $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `IsSemiLocalFactorization K L (SK ∪ T) φL φa φf` holds with the semi-local factor at $v$ taken to be, for $v\in T$, the function $x\mapsto\sum_{\iota:\mathrm{Fin}(ks_v)\to\mathrm{Fin}(ns_v)}\mathbf 1_{\text{semi-local integral set}}\bigl(\mathtt{semiLocalComponent}(\mathtt{localEmbed}_{ws_v}(\prod_m rT_v(\iota m)\cdot zs_v^{\,js_v}))^{-1}x\bigr)$ and $\varphi_S(v)$ otherwise, and with $\varphi_L$ bi-invariant under $\mathtt{levelOne}(N)\sqcap\mathtt{finiteAdelicGL2Subgroup}\,L$ and archimedean bi-finite of type $\mathrm{tys}_L$; and for every family $\mathrm{fam}$, indexed by the dependent functions $m$ assigning to each $v\in T$ an element of $\mathrm{Fin}\,2\to_0\mathbb N$, of functions on $\mathrm{GL}_2(\mathbb A_K)$ such that for each $m$ in the slot index $\mathtt{slotIndex}\,K\,L\,ws\,ks\,js\,T$ (the product over $v\in T$ of the supports of the Satake slot words) the function $\mathrm{fam}(m)$ is bi-invariant under $\mathtt{principalLevel}(N')\sqcap\mathtt{finiteAdelicGL2Subgroup}\,K$ and archimedean bi-finite of type $\mathrm{tys}_K$, $f_{a,K}$ is an archimedean test factor (a smooth function of the archimedean matrix entries with compact support), each $f_{S,K}(v)$ for $v\in S_K$ is a local test function (locally constant with compact support), and there is a finite test factor $f\!f$ (locally constant with compact support) such that $f\!f(h)$ equals the product over $v\in S_K\cup T$ of the factors $x\mapsto\sum_{\iota:\mathrm{Fin}(m_v 0)\to\mathrm{Fin}(nK_v)}\mathbf 1_{\text{local integral set}}\bigl((\prod_{m'} rK_v(\iota m')\cdot zK_v^{\,m_v 1})^{-1}x\bigr)$ for $v\in T$ and $f_{S,K}(v)$ otherwise, evaluated at the components of $h$, whenever all components of $h$ outside $S_K\cup T$ are integral, while $f\!f(h)=0$ as soon as some component outside $S_K\cup T$ fails to be integral, and $\mathrm{fam}(m)(g)=f_{a,K}(g_\infty)\,f\!f(g_{\mathrm{fin}})$ for all $g$; and such that $\varphi_L$ and $x\mapsto\sum_{m\in\mathtt{slotIndex}}\mathtt{slotFamilyCoeff}(m)\,\mathrm{fam}(m)(x)$ are matching at $\sigma^{-1}$ over $S_K\cup T$ — there exists $R_0\in\mathbb R$ such that for every $R\ge R_0$ the following hold.
--
--   Write $\Theta_L(x,y)=\sum^{\mathrm f}_{\delta}\varphi_L\bigl(x^{-1}\delta\,\sigma^{-1}(y)\bigr)$, the finsum over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted class has hyperbolic norm class, and let $C_L(x,\cdot)$ be the constant term, in the sense of [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) with respect to the adelic Borel structure and the Haar measure of $\mathbb A_L$ conditioned on the adelic box (the measure attached to the carrier pins `productionPinsOf` of $\Phi_L$, the levels $\mathtt{levelOne}(M)\sqcap\mathtt{finiteAdelicGL2Subgroup}\,L$, the Hecke generators and the adelic box) and the unipotent family $t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}$, of the function $y\mapsto\sum^{\mathrm f}_{\delta}\varphi_L(x^{-1}\delta\,\sigma^{-1}(y))$ over the $\delta\in\mathrm{GL}_2(L)$ with lower-left entry $0$ and $N_{L/K}(\delta_{00}/\delta_{11})\ne1$. Then: for every $x$, the function $z\mapsto\xi_L(z)\bigl(\Theta_L(x,zx)-\mathbf 1_{\{\,\mathtt{adelicHeight}_L>e^R\}}(zx)\,C_L(x,zx)\bigr)$ is integrable on $\Omega_L$ for $\nu_{Z,L}$, and the function of $x$ obtained by integrating it over $\Omega_L$ is integrable on $\mathtt{canonicalTruncationDomain}\,L\,\alpha\,\beta$ for `adelicGLHaar`.
--
--   Likewise, for every $\xi_K\in\Xi$ and every $m$ in the slot index, with $\mathcal K^{\mathrm{hyp}}_{\mathrm{fam}(m)}$ the hyperbolic part of the adelic kernel of $\mathrm{fam}(m)$ and $C_K(x,\cdot)$ the corresponding constant term (same unipotent family, the conditioned Haar measure attached to the pins of $\Phi_K$ with levels $\mathtt{principalLevel}(M)\sqcap\mathtt{finiteAdelicGL2Subgroup}\,K$, applied to $y\mapsto\sum^{\mathrm f}_{\gamma}\mathrm{fam}(m)(x^{-1}\gamma y)$ over the $\gamma\in\mathrm{GL}_2(K)$ with lower-left entry $0$ and $\gamma_{00}/\gamma_{11}\ne1$): for every $x$ the function $z\mapsto\xi_K(z)\bigl(\mathcal K^{\mathrm{hyp}}_{\mathrm{fam}(m)}(x,zx)-\mathbf 1_{\{\mathtt{adelicHeight}_K>e^R\}}(zx)\,C_K(x,zx)\bigr)$ is integrable on $\Omega_K$ for $\nu_{Z,K}$, and its $z$-integral is integrable in $x$ on $\mathtt{canonicalTruncationDomain}\,K\,\alpha\,\beta$.
--
--   Finally, for every $g\in C(X,\mathbb C)$ which is the monomial $g(x)=\prod_{v\in T}(x_{w'_v})_1^{\,ks_v}\bigl(\mathcal N(w'_v)^{-1}(x_{w'_v})_2\bigr)^{js_v}$,
--   $$\int_{\mathtt{canonicalTruncationDomain}\,L}\!\int_{\Omega_L}\xi_L(z)\bigl(\Theta_L(x,zx)-\mathbf 1_{\{\mathtt{adelicHeight}_L>e^R\}}(zx)C_L(x,zx)\bigr)\;-\;\ell\,\lambda\!\!\sum_{\xi_K\in\Xi}\sum_{m\in\mathtt{slotIndex}}\!\!\mathtt{slotFamilyCoeff}(m)\int_{\mathtt{canonicalTruncationDomain}\,K}\!\int_{\Omega_K}\xi_K(z)\bigl(\mathcal K^{\mathrm{hyp}}_{\mathrm{fam}(m)}(x,zx)-\mathbf 1_{\{\mathtt{adelicHeight}_K>e^R\}}(zx)C_K(x,zx)\bigr)\;=\;R\,\nu_h(g)+\Delta_h(g),$$
--   the $R$ on the right-hand side being the real parameter viewed as a complex number. In particular the same $\lambda$ serves for all admissible $T$ and all the remaining data, and the functionals $\Delta_h,\nu_h$ depend on $T$ and the Hecke data but not on $ks,js$, on the test functions or on $R$.
--
--   This is the hyperbolic (split) term in the comparison of the $\sigma^{-1}$-twisted trace formula for $\mathrm{GL}_2$ over $L$ with the untwisted one over $K$ in a cyclic extension of prime degree: after truncation above adelic height $e^R$ the difference of the two hyperbolic contributions is affine in $R$, with slope $\nu_h$ and intercept $\Delta_h$ read off from a functional on the compact space of Hecke tables, and with a single non-zero proportionality constant $\lambda$ valid for all finite sets $T$ of auxiliary places. It is used by the statement that extracts the intercept of the parabolic comparison, where the uniformity of $\lambda$ over place-sets is what makes the limiting argument possible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform.lean

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

theorem AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_hyperbolicTerm_sub_finrank_mul_const_mul_sum_eq_of_areMatchingAt_uniform
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
    ∃ lam : ℂ, lam ≠ 0 ∧
      ((∃ S' : Finset (HeightOneSpectrum (𝓞 K)), SK ⊆ S' ∧
      ∃ (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ),
        Continuous φ ∧ HasCompactSupport φ ∧
        AutomorphicForm.IsUnitFactorizableAboveOfType K L tysL
          (levelOne (𝓞 L) L N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup L) S' φ ∧
        Continuous f ∧ HasCompactSupport f ∧
        AutomorphicForm.IsUnitFactorizableOfTypeAt K tysK
          (principalLevel (𝓞 K) K N' ⊓ AutomorphicForm.finiteAdelicGL2Subgroup K) S' f ∧
        AutomorphicForm.AreMatchingAt K L σ.symm S' φ f ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S' →
          (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
            Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
          AutomorphicForm.AreMatchingLocal K L v σ.symm
            ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
            ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))) ∧
        (∑ ξK ∈ Ξ, (∫ x in ΦK, (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelCentralPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
              AutomorphicForm.adelicKernelEllipticPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ≠ 0) →
        (Module.finrank K L : ℂ) * lam = c₀) ∧
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
      ∃ Δh νh : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Δh g‖ < ε) ∧
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
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
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
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φL (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ.symm y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
        (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (R : ℂ) * νh g + Δh g := by sorry
