-- Prove2me | Theorems.Thm_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
-- name    : AutomorphicForm.slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0c18e739-7313-5966-a44b-54eb09046327
-- title:
--   Unweighted split-class expansion of the ground-field hyperbolic slope
-- statement:
--   Throughout, $K\subseteq L$ are number fields with $L/K$ finite and Galois, and the usual measurability/Borel and Haar typeclass assumptions on the idele groups and on $\mathrm{GL}_2$ of the adeles are in force.
--
--   **The window and the fundamental domains upstairs.** Reals $\alpha,\beta$ are given with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). A set $\Phi_L\subseteq\mathrm{GL}_2(\mathbb A_L)$ is contained in the determinant window $\{g:\ \|\det g\|_L\in[\alpha,\beta]\}$ (`hΦs`), where $\|\cdot\|_L$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of an idele for the additive Haar measure on $\mathbb A_L$, and $\Phi_L$ is a fundamental domain (`hΦ`) for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to that window. A Haar measure $\nu_{Z,L}$ on $\mathbb A_L^\times$ is fixed together with a fundamental domain $\Omega_L$ for the subgroup of principal ideles (`hΩL`).
--
--   **Galois data.** `D` is an idele Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, compatible with $L\to\mathbb A_L$ and continuous in each element; $\sigma\in\mathrm{Gal}(L/K)$ is such that every $\tau$ is an integral power of $\sigma^{-1}$ (`hgen`), and $[L:K]$ is prime (`hdeg`).
--
--   **Places.** $S_K$ is a finite set of finite places of $K$ and $S_L$ one of finite places of $L$, subject to: every place of $L$ above a place of $S_K$ lies in $S_L$ (`hSL`); $S_L$ is a union of fibres, i.e. $w\in S_L\iff w'\in S_L$ whenever $w,w'$ lie over the same place of $K$ (`hSsat`); and $\mathrm{ramificationIdx}'$ of $w$ over its underlying place equals $1$ whenever that place is not in $S_K$ (`hS`).
--
--   **The character upstairs.** $\xi_L$ is a homomorphism from the full subgroup of $\mathbb A_L^\times$ to $\mathbb C^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`), and takes the same value on $\det$ of the Hecke generators `heckeGen` at any two places $w,w'\notin S_L$ lying over the same place of $K$ (`hξσ`).
--
--   **Level, types and local components.** $N$ is an ideal of $\mathcal O_L$ all of whose prime divisors lie in $S_L$ (`hN`); `tysL` is an archimedean type family for $L$; $\varphi_a$ is a function on $\mathrm{GL}_2$ of the infinite adeles of $L$ and $\varphi_S$ a family of functions on $\mathrm{GL}_2(L\otimes_K K_v)$ indexed by finite places $v$ of $K$; $f_{a,K}$ and $f_{S,K}$ are the corresponding data over $K$. A set $X$ of functions from finite places of $L$ to $\mathbb C\times\mathbb C$ is compact (`hXc`) and contains (`hX`) the set of those $x$ which vanish at every $w\in S_L$ and for which, at every $w\notin S_L$: $(x\,w)_2=\mathrm{cNorm}(w)\,\xi_L(\det\mathrm{heckeGen}_w)$, $\|(x\,w)_1\|\le(\mathrm{absNorm}(w)+1)\sqrt{\|\xi_L(\det\mathrm{heckeGen}_w)\|}$, and $\overline{(x\,w)_1}=\overline{(x\,w)_2}\,\|(x\,w)_2\|^{-1}(x\,w)_1$.
--
--   **The ground-field side.** $\Phi_K$ is contained in the corresponding determinant window over $K$ (`hΦKs`) and is a fundamental domain for the image of $\mathrm{GL}_2(K)$ there (`hΦK`); $\nu_{Z,K}$ is a Haar measure on $\mathbb A_K^\times$ with fundamental domain $\Omega_K$ for the principal ideles (`hΩK`). $\Xi$ is a finite set of homomorphisms from the full subgroup of $\mathbb A_K^\times$ to $\mathbb C^\times$, characterised (`hΞ`) by: $\xi\in\Xi$ if and only if $\xi$ is continuous, trivial on principal ideles, and satisfies $\xi(\mathrm{idelicNorm}\,z)=\xi_L(z)$ for all $z\in\mathbb A_L^\times$, the norm being that of the base-change datum [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87). Further, $N'$ is an ideal of $\mathcal O_K$ whose prime divisors lie in $S_K$ (`hN'`), `tysK` is an archimedean type family for $K$, and $c_0\in\mathbb C$.
--
--   **The elliptic–central comparison `hgeo`.** For every finite set $S'\supseteq S_K$ of finite places of $K$, every continuous compactly supported $\varphi$ on $\mathrm{GL}_2(\mathbb A_L)$ which is unit-factorizable above $S'$ of type `tysL` for the level $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, every continuous compactly supported $f$ on $\mathrm{GL}_2(\mathbb A_K)$ unit-factorizable at $S'$ of type `tysK` for $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$, with $\varphi$ and $f$ matching at $S'$ relative to $\sigma^{-1}$, and with the indicators of the semi-local and local integral sets matching locally at every $v\notin S'$ all of whose places above are unramified, one has the identity
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\bigl(x^{-1}\,\delta\,\sigma^{-1}\!\cdot\!(z\,x)\bigr)\,d\nu_{Z,L}\,d\mu_L = c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\bigl(K^{\mathrm{cent}}_f(x,zx)+K^{\mathrm{ell}}_f(x,zx)\bigr)\,d\nu_{Z,K}\,d\mu_K,$$
--   where the $\delta$-sum runs over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted norm class maps under [`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766) to the conjugacy class of some $\gamma\in\mathrm{GL}_2(K)$ lying in the elliptic or the central cell, the twisting of $z\,x$ is by `sigmaAdelicAct K L D σ.symm`, and $K^{\mathrm{cent}}_f,K^{\mathrm{ell}}_f$ are the central and elliptic parts of the adelic kernel, the sums of $f(x^{-1}\gamma y)$ over the central, resp. elliptic, cell.
--
--   **Conclusion.** Under these hypotheses, the following holds for all data as listed.
--
--   A finite set $T$ of finite places of $K$ disjoint from $S_K$ with $2\le\#T$, such that no place of $L$ above a place of $T$ lies in $S_L$; a choice $ws$ of an extension $(ws\,v)$ to $L$ of each place $v$ of $K$, and a map $w'$ of places with $(w'\,v)$ the ideal $\sigma^{-1}\!\cdot(ws\,v)$ for $v\in T$; elements $\varpi_v$ of the valuation ring of $L$ at $ws\,v$, irreducible and with nonzero image in the completion for $v\in T$; integers $n_v$ and families $r_{T,v}:\mathrm{Fin}(n_v)\to\mathrm{GL}_2(L_{ws\,v})$ forming, for $v\in T$, a Hecke coset system for the integral subgroup and the element $\mathrm{diagPi}(\varpi_v)=\mathrm{diag}(\varpi_v,1)$ (each representative lies in the double coset, the representatives cover it modulo the integral subgroup, and the induced map to cosets is injective); elements $z_v\in\mathrm{GL}_2(L_{ws\,v})$ equal to $\varpi_v$ times the identity matrix for $v\in T$; and, over $K$, the analogous data $\varpi_{K,v}$, $n_{K,v}$, $r_{K,v}$ (Hecke coset systems for $\mathrm{diag}(\varpi_{K,v},1)$) and central scalars $z_{K,v}=\varpi_{K,v}\cdot 1$.
--
--   Exponent functions $k,j$ on the finite places of $K$; a continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb A_L)$ and a function $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that `hSLF` holds: $\varphi_L$ is semi-locally factorized over $S_K\cup T$ with archimedean factor $\varphi_a$ (a smooth compactly supported function of the archimedean matrix entries), finite factor $\varphi_f$ (locally constant with compact support), semi-local test components at the places of $S_K\cup T$, $\varphi_f$ equal to the product of those components on elements integral outside $S_K\cup T$ and zero otherwise, and $\varphi_L(g)=\varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$; the prescribed components are, at $v\in T$, the Hecke-word functions
--   $$x\mapsto\sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\text{semi-local integral set}}\Bigl(\bigl(\text{semi-local component at }v\text{ of the local embedding at }ws\,v\text{ of }\textstyle\prod_m r_{T,v}(\iota\,m)\cdot z_v^{\,j_v}\bigr)^{-1}x\Bigr),$$
--   and $\varphi_S\,v$ otherwise. Moreover $\varphi_L$ is bi-invariant under $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$ (`hbi`) and archimedeanly bi-finite of type `tysL` (`harch`).
--
--   A family $\mathrm{fam}$ of functions on $\mathrm{GL}_2(\mathbb A_K)$ indexed by the slot data $m$ (assignments $v\in T\mapsto(\mathrm{Fin}\,2\to_{\!f}\mathbb N)$), such that for every $m$ in `SatakeCombination.slotIndex K L ws k j T` the hypothesis `hfam` holds: $\mathrm{fam}\,m$ is bi-invariant under $\mathrm{principalLevel}(N')\sqcap\mathrm{finiteAdelicGL2Subgroup}$, archimedeanly bi-finite of type `tysK`, $f_{a,K}$ is an archimedean test factor, each $f_{S,K}\,v$ for $v\in S_K$ is a local test function, and there is a finite test factor $f\!f$ (locally constant, compactly supported) which, on elements integral outside $S_K\cup T$, equals the product over $v\in S_K\cup T$ of the components — at $v\in T$ the Hecke word $x\mapsto\sum_{\iota:\mathrm{Fin}((m_v)_0)\to\mathrm{Fin}(n_{K,v})}\mathbf 1_{\text{local integral set}}\bigl((\prod_m r_{K,v}(\iota\,m)\cdot z_{K,v}^{(m_v)_1})^{-1}x\bigr)$, and $f_{S,K}\,v$ otherwise — vanishes on elements non-integral at some place outside $S_K\cup T$, and satisfies $\mathrm{fam}\,m(g)=f_{a,K}(g_\infty)\,f\!f(g_{\mathrm{fin}})$. The function $\varphi_L$ matches, at $S_K\cup T$ and relative to $\sigma^{-1}$, the combination $x\mapsto\sum_m \mathrm{slotFamilyCoeff}(m)\,\mathrm{fam}\,m(x)$ over the slot index (`hmatch`).
--
--   A character $\xi_K\in\Xi$, a slot $m$ in the slot index, complex numbers $A,B$ and a real $R_0$ such that the truncated hyperbolic term is affine in $R$: for every $R\ge R_0$,
--   $$\int_{\mathcal F_K(\alpha,\beta)}\int_{\Omega_K}\xi_K(z)\Bigl(K^{\mathrm{hyp}}_{\mathrm{fam}\,m}(x,zx)-\mathbf 1_{\{H_K>e^{R}\}}(zx)\cdot C(zx)\Bigr)d\nu_{Z,K}\,d\mu_K=R\,A+B,$$
--   where $\mathcal F_K(\alpha,\beta)$ is the canonical truncation domain of $K$ for the window $[\alpha,\beta]$, $K^{\mathrm{hyp}}$ is the hyperbolic part of the adelic kernel (the sum of $\mathrm{fam}\,m(x^{-1}\gamma y)$ over the hyperbolic cell), $H_K$ is the adelic height, and $C$ is the constant term, taken with respect to the conditional additive adelic measure on `adelicBox K` supplied by `productionPinsOf` and the unipotent one-parameter family $t\mapsto\mathrm{unipotentGL2}(t)$, of the function $y\mapsto\sum_\gamma\mathrm{fam}\,m(x^{-1}\gamma y)$, the sum running over $\gamma\in\mathrm{GL}_2(K)$ with $\gamma_{10}=0$ and $\gamma_{00}/\gamma_{11}\ne1$.
--
--   A descent datum $D_K$ for $K/K$ together with `hgenK` (automatic, the Galois group being trivial); a closed subgroup $H_K\le\mathrm{GL}_2(\mathbb A_K)$ characterised (`hHK`) as the set of $h$ with $h_{10}=0$, $h_{01}=0$ and $\mathrm{sigmaAdelicAct}(D_K,1)(h)\,h^{-1}$ central; a Haar measure $\mu_{H_K}$ on $H_K$ which is also right invariant.
--
--   A subgroup $\Lambda_{0,K}\le\mathrm{GL}_2(K)$ characterised (`hΛ₀K`) by $\gamma_{10}=0$, $\gamma_{01}=0$ and $\gamma_{00}/\gamma_{11}$ in the range of $\mathrm{algebraMap}\,K\,K$ (the last clause being vacuous); a constant $\kappa_{0,K}>0$; a set $\Omega_K'\subseteq H_K$ which is a fundamental domain for the image of $\Lambda_{0,K}$ under `globalPoints`, viewed inside $H_K$, with respect to $\mu_{H_K}$ (`hΩK'`). The two shell-volume hypotheses state: for all $y\in\mathrm{GL}_2(\mathbb A_K)$ and all $R$, the upper integral over $\Omega_K'$ of the enorm of the product of the window indicator at $h\,y$ with $1-\mathbf 1_{\{H_K>e^R\}}(hy)-\mathbf 1_{\{H_K(w\,\cdot)>e^R\}}(hy)$ equals $\kappa_{0,K}\,|2R-\log H_K(y)-\log H_K(w\,y)|$ (`hκ₀K`), $w$ being the adelic Weyl element; and (`hκ₀K'`) whenever $H_K(y)H_K(wy)\le e^{2R}$ the same integrand is integrable on $\Omega_K'$ and its integral equals $\kappa_{0,K}\bigl(2R-\log H_K(y)-\log H_K(wy)\bigr)$.
--
--   A finite set $\Delta_K^{\mathrm{fin}}\subseteq\mathrm{GL}_2(K)$ with: every member diagonal with ratio $\gamma_{00}/\gamma_{11}\ne1$ (`hΔKf`); the ratio map injective on it (`hΔKinj`); for every member $\gamma$ an element $u\in K^\times$ with $u\ne1$, $\gamma=\mathrm{diag}(u,1)$ and $\mathrm{diag}(u^{-1},1)\in\Delta_K^{\mathrm{fin}}$, so that the set consists of such representatives and is closed under inversion (`hΔKinv`); and completeness for $\mathrm{fam}\,m$ (`hΔKc`): if $u\in K^\times$, $u\ne1$, and no member of $\Delta_K^{\mathrm{fin}}$ has ratio $u$, then $\mathrm{fam}\,m\bigl(x^{-1}(z\cdot\mathrm{diag}(u,1))x\bigr)=0$ for all ideles $z$ and all $x\in\mathrm{GL}_2(\mathbb A_K)$.
--
--   Unfolding constants: $c_{H_K}>0$ with $\int_{H_K}g(h)\,d\mu_{H_K}=c_{H_K}\int\! g\bigl(z(p_1)\,\mathrm{diag}(p_2,1)\bigr)d(\nu_{Z,K}\times\nu_{Z,K})$ for every $g$ (`hHKμ`), $z(\cdot)$ denoting the central scalar; and $c_{\tau_K}>0$ with a family of measures $\tau_K(\gamma)$ on the centralisers of $\mathrm{globalPoints}(\gamma)$, each Haar (`hτK`), satisfying for $\gamma\in\Delta_K^{\mathrm{fin}}$ and every $g$ the unfolding $\int g(s)\,d\tau_K(\gamma)=c_{\tau_K}\int g(\mathrm{diag}(p_1,p_2))\,d(\nu_{Z,K}\times\nu_{Z,K})$ (`hτKc`).
--
--   Finally, functions $I_K,J_K$ of a class $\gamma$ and an idele $z$ such that for $\gamma\in\Delta_K^{\mathrm{fin}}$ and all $z$: $I_K(\gamma,z)$ is an orbital integral of $g\mapsto\mathrm{fam}\,m(z\,g)$ at $\mathrm{globalPoints}(\gamma)$ for the measures `adelicGLHaar` and $\tau_K(\gamma)$, i.e. equals $\int \mathrm{fam}\,m(z\,x^{-1}\gamma x)\,s(x)\,d\mu_K$ for some real section weight $s$ satisfying `IsSectionFnOn` (`hIK`); and $J_K(\gamma,z)$ is the corresponding weighted orbital integral with weight $x\mapsto-\log H_K(x)-\log H_K(w\,x)$ (`hJK`).
--
--   Then both of the following hold:
--
--   1. for every $\gamma\in\Delta_K^{\mathrm{fin}}$ the function $z\mapsto\xi_K(z)\,I_K(\gamma,z)$ is integrable with respect to $\nu_{Z,K}$;
--
--   2. the slope is the unweighted sum
--   $$A=\sum_{\gamma\in\Delta_K^{\mathrm{fin}}}\kappa_{0,K}\Bigl(\frac{c_{\tau_K}}{c_{H_K}}\int_{\mathbb A_K^\times}\xi_K(z)\,I_K(\gamma,z)\,d\nu_{Z,K}\Bigr).$$
--
--   No factor $2$ and no class-dependent weight occurs, and $B$, $J_K$ and the weighted orbital integrals do not appear in the conclusion.
--
--   This is the ground-field half of the comparison of hyperbolic terms in the base-change trace formula for $\mathrm{GL}_2$: the slope $A$ of the $R$-affine truncated hyperbolic term attached to one member $\mathrm{fam}\,m$ of a matched family of Hecke-word test functions is identified with a sum of $\xi_K$-folded split orbital integrals, indexed by an inversion-closed, ratio-injective finite set of representatives $\mathrm{diag}(u,1)$ with $u\ne1$, in the unweighted indexing convention. It is used by [`AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine`](thm.html#AutomorphicForm.exists_const_forall_exists_windingDatum_sub_finrank_mul_const_mul_sum_eq_sum_mul_coeff_of_hyperbolicTerm_eq_affine), where the two sides of the hyperbolic comparison are matched slot by slot.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine.lean

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
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_HaarQuotient
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel
open LanglandsTunnell.CubicInduction (diagUnits2)

open AutomorphicForm in
open scoped TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.slope_eq_sum_unweighted_classIntegral_diagUnits2_of_inversionClosed_of_hyperbolicTerm_eq_affine
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
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ) (hφL : Continuous φL) (hφLc : HasCompactSupport φL)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
        (hSLF : IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))
        (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φL)
        (harch : IsArchBiFinite L tysL φL)
        (fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ)
        (hfam : ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g))
        (hmatch : AreMatchingAt K L σ.symm (SK ∪ T) φL
          (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x)),
      ∀ (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ), ξK ∈ Ξ →
      ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      ∀ (A B : ℂ) (R₀ : ℝ),
      (∀ R : ℝ, R₀ ≤ R →
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
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * A + B) →
      ∀ (DK : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
        (hgenK : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K K DK 1 h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 K) K)))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]

    (Λ₀K : Subgroup (GL (Fin 2) K))
    (hΛ₀K : ∀ γ : GL (Fin 2) K, γ ∈ Λ₀K ↔ (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Set.range (algebraMap K K))
    (κ₀K : ℝ) (hκ₀Kpos : 0 < κ₀K) (ΩK' : Set HK)
    (hΩK' : IsFundamentalDomain ((Λ₀K.map (AutomorphicForm.globalPoints (𝓞 K) K)).subgroupOf HK) ΩK' μHK)
    (hκ₀K : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
      ∫⁻ h in ΩK', ‖Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))‖ₑ ∂μHK =
        ENNReal.ofReal (κ₀K * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))|))

    (hκ₀K' : ∀ (y : AdelicGL2 (𝓞 K) K) (R : ℝ),
        (NumberField.AdelicHeight.adelicHeight K y *
            NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : HK => Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y))) ΩK' μHK ∧
          ∫ h in ΩK', Set.indicator {g : AdelicGL2 (𝓞 K) K | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 K) K | Real.exp R < NumberField.AdelicHeight.adelicHeight K y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 K) K |
                Real.exp R < NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 K) K) * y)) ∂μHK =
            ((κ₀K * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight K y)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * y))) : ℝ) : ℂ)))

    (ΔKfin : Finset (GL (Fin 2) K))
    (hΔKf : ∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hΔKinj : ∀ γ ∈ ΔKfin, ∀ γ' ∈ ΔKfin,
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (γ' : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ' : Matrix (Fin 2) (Fin 2) K) 1 1 → γ = γ')
    (hΔKinv : ∀ γ ∈ ΔKfin, ∃ u : Kˣ, (u : K) ≠ 1 ∧ γ = diagUnits2 u 1 ∧ diagUnits2 u⁻¹ 1 ∈ ΔKfin)
    (hΔKc : ∀ u : Kˣ, (u : K) ≠ 1 →
      (∀ γ ∈ ΔKfin, (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ (u : K)) →
        ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
          fam m (x⁻¹ * (AutomorphicForm.centralScalar (𝓞 K) K z *
            diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) * x) = 0)

    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔKfin, ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ γ ∈ ΔKfin, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK γ z))
    (hJK : ∀ γ ∈ ΔKfin, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (JK γ z)),
      (∀ γ ∈ ΔKfin, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z) νZK) ∧
      A = ∑ γ ∈ ΔKfin, (κ₀K : ℂ) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by sorry
