-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
-- name    : AutomorphicForm.exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e55fb135-e77d-5720-ba18-da3d28bc30ed
-- title:
--   Hyperbolic slope and intercept as sums of orbital integrals
-- statement:
--   **Ambient data.** $K$ and $L$ are number fields with $L$ a finite Galois extension of $K$, and $0<\alpha<\beta$ are reals. Write $\mathbb{A}_F$ for the adele ring of a number field $F$ and $\|\cdot\|$ for [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of the distributive Haar character of an idele.
--
--   Over $L$: a set `ΦL` of adelic matrices contained in the determinant shell $\{g:\|\det g\|\in[\alpha,\beta]\}$ (`hΦs`) and, by `hΦ`, a fundamental domain for the translation action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` on that shell, with respect to `adelicGLHaar` restricted to the shell; a Haar measure `νZL` on $\mathbb{A}_L^\times$ together with a fundamental domain `ΩL` for the image of $L^\times$ (`hΩL`); a Galois descent datum `D` for the adeles of $L$ over $K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with the action on $L$ and continuous); an element $\sigma$ of $\mathrm{Gal}(L/K)$ with `hgen`, every element of the group being an integer power of $\sigma^{-1}$, and `hdeg`, $[L:K]$ prime.
--
--   Place bookkeeping: finite sets `SK` of finite places of $K$ and `SL` of finite places of $L$ with `hSL` (every place of $L$ lying over a place in `SK` belongs to `SL`), `hSsat` (membership in `SL` depends only on the place of $K$ below), and `hS` (at every place $w$ of $L$ whose place below avoids `SK`, the ramification index `Ideal.ramificationIdx'` equals $1$).
--
--   A character `ξL` of the full subgroup of $\mathbb{A}_L^\times$ with values in $\mathbb{C}^\times$, continuous (`hξc`), trivial on principal ideles (`hξt`), and satisfying `hξσ`: for places $w,w'$ of $L$ outside `SL` lying over the same place of $K$, the values of `ξL` at $\det$ of the Hecke generators `heckeGen` at $w$ and at $w'$ agree. An ideal $N$ of $\mathcal{O}_L$ with `hN` (every place dividing $N$ lies in `SL`), an archimedean type family `tysL` for $L$, and test-function ingredients: `φa` on $\mathrm{GL}_2$ of the infinite adeles of $L$, semi-local components `φS v` on $\mathrm{GL}_2(L\otimes_K K_v)$, and the analogues `faK`, `fSK` over $K$.
--
--   A compact set $X$ (`hXc`) of families $x$ indexed by the finite places of $L$ with values in $\mathbb{C}\times\mathbb{C}$, containing (`hX`) every family that vanishes on `SL` and for which, at each $w\notin$ `SL`, the second coordinate equals `HeckeEigensystem.cNorm w` times `ξL` of $\det$ of `heckeGen` at $w$, the first coordinate has norm at most $(\mathrm{N}w+1)$ times the square root of the norm of that value of `ξL`, and $\overline{(x_w)_1}=\overline{(x_w)_2}\,\|(x_w)_2\|^{-1}(x_w)_1$.
--
--   Over $K$: a set `ΦK` inside the determinant shell (`hΦKs`) which is a fundamental domain for the image of $\mathrm{GL}_2(K)$ on that shell (`hΦK`); a Haar measure `νZK` on $\mathbb{A}_K^\times$ with fundamental domain `ΩK` for the image of $K^\times$ (`hΩK`); a finite set $\Xi$ of characters of the full subgroup of $\mathbb{A}_K^\times$ which, by `hΞ`, consists exactly of the continuous characters trivial on principal ideles whose composition with the idelic norm of the base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87) equals `ξL`; an ideal $N'$ of $\mathcal{O}_K$ with `hN'`; an archimedean type family `tysK`.
--
--   Finally a constant $c_0\in\mathbb{C}$ and the comparison hypothesis `hgeo`: for every finite set $S'\supseteq$ `SK` and every pair of functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which are continuous, compactly supported, unit-factorisable above $S'$ of type `tysL` for `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` respectively unit-factorisable at $S'$ of type `tysK` for `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`, matching at $S'$ with respect to $\sigma^{-1}$, and such that at every $v\notin S'$ all of whose places above are unramified the indicator of `semiLocalIntegralSet K L v` and the indicator of `localIntegralSet K v` match locally, the $\xi_L$-folded twisted elliptic-plus-central term for $L$ — the integral over `ΦL` in $x$, then over `ΩL` in $z$, of `ξL` $(z)$ times the finite sum over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted norm class ([`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766)) is the conjugacy class of some $\gamma$ in `ellipticCell K ∪ centralCell K`, of $\varphi\bigl(x^{-1}\,\delta\,{}^{\sigma^{-1}}\!(z x)\bigr)$ with the twisted action `sigmaAdelicAct K L D σ.symm` — equals $c_0$ times the sum over $\xi_K\in\Xi$ of the corresponding integrals over `ΦK` and `ΩK` of $\xi_K(z)$ times `adelicKernelCentralPart K f x (z\cdot x)` $+$ `adelicKernelEllipticPart K f x (z\cdot x)`.
--
--   **Conclusion.** For every finite set $T$ of finite places of $K$ that is disjoint from `SK`, has at least two elements, and all of whose places of $L$ above it avoid `SL`; for every choice `ws` of an extension $w_v\mid v$ in $L$ for each $v$, every map `w'` with $(w'_v)$ the ideal $\sigma^{-1}\cdot w_v$ for $v\in T$; every choice `ϖs` of elements of the valuation rings at the $w_v$ that are irreducible and have nonzero image in the completion for $v\in T$ (`hϖs0`); every `ns`, `rTs` such that for $v\in T$ the family `rTs v` is a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the double coset of [`LocalGL2.diagPi (ϖs v)`](def/LocalLanglands_HeckeCosetLocal.html#L68) relative to [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) at $w_v$; every `zs` with $z_v$ the scalar matrix $\varpi_v\cdot 1$ for $v\in T$; every analogous $K$-side data `ϖKs`, `nKs`, `rKs`, `zKs` subject to the same conditions at the places $v\in T$ of $K$; every pair of exponent functions `ks`, `js`; every continuous compactly supported `φL` on $\mathrm{GL}_2(\mathbb{A}_L)$ and every finite-part function `φf` such that `hSLF` holds, i.e. `φL` admits the semi-local factorisation over `SK ∪ T` with archimedean factor `φa`, finite factor `φf` and semi-local factors given at $v\in T$ by
--   $$x\mapsto \sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf 1_{\mathrm{semiLocalIntegralSet}\,K\,L\,v}\Bigl(\bigl(\mathrm{semiLocalComponent}\,K\,L\,v\bigl(\mathrm{localEmbed}_{w_v}\bigl(\textstyle\prod_m r_{T,v}(\iota m)\cdot z_v^{\,j_v}\bigr)\bigr)\bigr)^{-1}x\Bigr)$$
--   and by `φS v` at $v\notin T$; with `φL` bi-invariant under `levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` (`hbi`) and archimedean-bi-finite of type `tysL` (`harch`); and for every family `fam` of functions on $\mathrm{GL}_2(\mathbb{A}_K)$ indexed by the slot indices (functions assigning to each $v\in T$ an element of $\mathrm{Fin}\,2\to_{0}\mathbb{N}$) such that `hfam` holds: for each $m$ in `SatakeCombination.slotIndex K L ws ks js T`, `fam m` is bi-invariant under `principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K`, archimedean-bi-finite of type `tysK`, `faK` is an archimedean test factor, each `fSK v` for $v\in$ `SK` is a local test function, and there is a finite test factor `ff` which, on matrices all of whose components outside `SK ∪ T` lie in the local integral sets, equals the product over $v\in$ `SK ∪ T` of the factor $\sum_{\iota:\mathrm{Fin}(m_v(0))\to \mathrm{Fin}(n_{K,v})}\mathbf 1_{\mathrm{localIntegralSet}\,K\,v}\bigl((\prod_m r_{K,v}(\iota m)\, z_{K,v}^{\,m_v(1)})^{-1}x\bigr)$ at $v\in T$ and `fSK v` otherwise, which vanishes when some component outside `SK ∪ T` fails to be integral, and with `fam m g` $=$ `faK` of the archimedean part times `ff` of the finite part; and such that `hmatch` holds: `φL` and $x\mapsto\sum_m$ `SatakeCombination.slotFamilyCoeff` $\cdot$ `fam m x` match at `SK ∪ T` with respect to $\sigma^{-1}$ —
--
--   the following holds for every $\xi_K\in\Xi$, every slot index $m$, all $A,B\in\mathbb{C}$ and every $R_0\in\mathbb{R}$ subject to the affineness hypothesis: for all $R\ge R_0$,
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta}\ \int_{\Omega_K}\xi_K(z)\Bigl(\mathrm{adelicKernelHyperbolicPart}\,K\,(\mathrm{fam}\,m)\,x\,(z\cdot x)-\mathbf 1_{\{H>e^{R}\}}(z\cdot x)\,C_x(z\cdot x)\Bigr)\,d\nu_{Z_K}\,d\,\mathrm{adelicGLHaar}=R\,A+B,$$
--   where $H$ is [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158), the hyperbolic part is the finite sum of `fam m` $(x^{-1}\gamma y)$ over $\gamma\in$ `hyperbolicCell K`, and $C_x$ is the constant term of $y\mapsto\sum_\gamma$ `fam m` $(x^{-1}\gamma y)$, the sum being over $\gamma\in\mathrm{GL}_2(K)$ with $\gamma_{10}=0$ and $\gamma_{00}/\gamma_{11}\neq 1$, formed by integrating the unipotent translates $y\mapsto$ `unipotentGL2 t` $\cdot y$ against the measure of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the additive adelic Haar measure of $K$ conditioned on `adelicBox K`;
--
--   and subject to the following further $K$-side data and hypotheses. A descent datum `DK` for $\mathbb{A}_K$ over $K$ and `hgenK` (every element of $\mathrm{Gal}(K/K)$ is an integer power of $1$). A closed subgroup `HK` of $\mathrm{GL}_2(\mathbb{A}_K)$ characterised by `hHK` as consisting of the $h$ with $h_{10}=h_{01}=0$ and `sigmaAdelicAct K K DK 1 h` $\cdot h^{-1}$ central, carrying a right-invariant Haar measure `μHK`. A subgroup $\Lambda_{0K}$ of $\mathrm{GL}_2(K)$ characterised by `hΛ₀K` as the $\gamma$ with $\gamma_{10}=\gamma_{01}=0$ and $\gamma_{00}/\gamma_{11}$ in the range of `algebraMap K K`; a constant $\kappa_{0K}>0$ and a fundamental domain $\Omega_K'$ for the image of $\Lambda_{0K}$ inside `HK` (`hΩK'`); the two volume computations `hκ₀K` and `hκ₀K'`: for all $y$ and $R$, the lower integral over $\Omega_K'$ of the extended norm of
--   $$\mathbf 1_{\{\|\det\|\in[\alpha,\beta]\}}(h y)\Bigl(1-\mathbf 1_{\{H>e^R\}}(h y)-\mathbf 1_{\{H(\mathrm{adelicWeyl}\cdot\,\cdot)>e^R\}}(h y)\Bigr)$$
--   equals `ENNReal.ofReal` of $\kappa_{0K}\,\bigl|2R-\log H(y)-\log H(\mathrm{adelicWeyl}\cdot y)\bigr|$, and, whenever $H(y)\,H(\mathrm{adelicWeyl}\cdot y)\le e^{2R}$, that same function is integrable on $\Omega_K'$ and its integral equals $\kappa_{0K}\bigl(2R-\log H(y)-\log H(\mathrm{adelicWeyl}\cdot y)\bigr)$. A set $\Delta_K\subseteq\mathrm{GL}_2(K)$ each of whose elements $t$ is diagonal with algebra norm over $K$ of $t_{00}/t_{11}$ different from $1$ (`hΔKd`), with `hΔKdisj`: for distinct $t,t'\in\Delta_K$ the sets of $\delta$ for which some $g$ makes $t^{-1}(g^{-1}\delta\,g)$ central are disjoint, and `hΔKcov`: the set of $\delta$ whose twisted norm class for $\sigma=1$ is the conjugacy class of some element of `hyperbolicCell K` is contained in the union of these sets over $t\in\Delta_K$. Unfolding constants: $c_{H_K}>0$ with `hHKμ`, stating that integration of any function over `HK` against `μHK` equals $c_{H_K}$ times its integral over pairs of ideles of $g\bigl(z_1\cdot 1\cdot\mathrm{diagUnits2}(z_2,1)\bigr)$ against $\nu_{Z_K}\times\nu_{Z_K}$; $c_{\tau_K}>0$, Haar measures $\tau_K(\gamma)$ on the centraliser of `globalPoints` $\gamma$ for each $\gamma\in\mathrm{GL}_2(K)$ (`hτK`), with `hτKc`: for $\gamma\in\Delta_K$, integration over that centraliser equals $c_{\tau_K}$ times the integral over pairs of ideles of $g(\mathrm{diagUnits2}(z_1,z_2))$. Finally functions $I_K,J_K$ of a matrix and an idele such that, for $\gamma\in\Delta_K$ and every $z$, $I_K(\gamma,z)$ is an orbital integral of $g\mapsto$ `fam m` $(z\cdot g)$ at `globalPoints` $\gamma$ for $\tau_K(\gamma)$ in the sense of `IsOrbitalIntegralOn` (`hIK`), and $J_K(\gamma,z)$ is a weighted orbital integral of the same function with weight $x\mapsto-\log H(x)-\log H(\mathrm{adelicWeyl}\cdot x)$ (`hJK`).
--
--   Under all of this, there exists a finite set $\Delta_f\subseteq\Delta_K$ such that for every finite set $S$ with $\Delta_f\subseteq S\subseteq\Delta_K$ the following four assertions hold: for each $t\in S$ the function $z\mapsto\xi_K(z)\,I_K(t,z)$ is $\nu_{Z_K}$-integrable; for each $t\in S$ the function $z\mapsto\xi_K(z)\,J_K(t,z)$ is $\nu_{Z_K}$-integrable;
--   $$A=\sum_{t\in S}2\,\kappa_{0K}\,\varepsilon_t\cdot\frac{c_{\tau_K}}{c_{H_K}}\int_{\mathbb{A}_K^\times}\xi_K(z)\,I_K(t,z)\,d\nu_{Z_K},$$
--   and
--   $$B=\sum_{t\in S}\kappa_{0K}\,\varepsilon_t\cdot\frac{c_{\tau_K}}{c_{H_K}}\int_{\mathbb{A}_K^\times}\xi_K(z)\,J_K(t,z)\,d\nu_{Z_K},$$
--   where $\varepsilon_t=\tfrac12$ if the algebra norm over $K$ of $t_{00}/t_{11}$ equals $-1$ and $\varepsilon_t=1$ otherwise.
--
--   This is the class-by-class evaluation of the hyperbolic contribution to the Arthur–Selberg trace formula for $\mathrm{GL}(2)$ over the ground field $K$: granted that the $\xi_K$-folded truncated hyperbolic term of a factorisable test function is affine in the truncation parameter $R$, its slope and its intercept are identified, over any sufficiently large finite set of diagonal class representatives, with finite sums of plain and of weighted orbital integrals, weighted by the centre-unfolding constants $\kappa_{0K}$ and $c_{\tau_K}/c_{H_K}$ and by the factor $\tfrac12$ at the class of ratio $-1$. It feeds the winding and Satake-combination steps of the hyperbolic-term comparison for cyclic base change, and is used by three downstream results on the hyperbolic slope and its Satake–Laurent expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine.lean

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

theorem AutomorphicForm.exists_finset_forall_slope_eq_sum_classIntegral_and_intercept_eq_sum_weightedClassIntegral_of_hyperbolicTerm_eq_affine
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

    (ΔK : Set (GL (Fin 2) K))
    (hΔKd : ∀ t ∈ ΔK, (t : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1)
    (hΔKdisj : ∀ t ∈ ΔK, ∀ t' ∈ ΔK, t ≠ t' →
      Disjoint {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)}
        {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})
    (hΔKcov : {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgenK (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ ΔK, {δ : GL (Fin 2) K | ∃ g : GL (Fin 2) K,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K) g) ∈ Subgroup.center (GL (Fin 2) K)})

    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : ∀ γ : GL (Fin 2) K,
      Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))))
    (hτK : ∀ γ : GL (Fin 2) K, (τK γ).IsHaarMeasure)
    (hτKc : ∀ γ ∈ ΔK, ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
          g (s : AdelicGL2 (𝓞 K) K) ∂(τK γ) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK γ z))
    (hJK : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) (τK γ)
          (fun g : AdelicGL2 (𝓞 K) K => fam m (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (JK γ z)),
      ∃ Δf : Finset (GL (Fin 2) K), (↑Δf ⊆ ΔK) ∧
      ∀ S : Finset (GL (Fin 2) K), Δf ⊆ S → (↑S ⊆ ΔK) →
      (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z) νZK) ∧
      (∀ t ∈ S, Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z) νZK) ∧
      (A = ∑ t ∈ S, 2 * ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK t z ∂νZK)) ∧
      (B = ∑ t ∈ S, ((κ₀K : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) K) 0 0 / (t : Matrix (Fin 2) (Fin 2) K) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          (((cτK / cHK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK t z ∂νZK)) := by sorry
