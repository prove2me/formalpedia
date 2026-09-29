-- Prove2me | Theorems.Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
-- name    : AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/e5971456-440d-50ac-80e3-1751410ee6cb
-- title:
--   Uniform transfer constant for twisted hyperbolic intercepts
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite and Galois, and $\alpha,\beta$ are reals with $0<\alpha<\beta$.
--
--   **Global windows and fundamental domains.** On the $L$-side: `ΦL` is a subset of $\mathrm{GL}_2(\mathbb{A}_L)$ contained, by `hΦs`, in the shell $\{g : \mathrm{ideleNorm}_L(\det g)\in[\alpha,\beta]\}$ (the idele norm being the modulus of the `distribHaarChar` of the adele ring), and which by `hΦ` is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on that shell, for the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to it; `νZL` is a Haar measure on the idele group $\mathbb{A}_L^\times$ and `ΩL` is, by `hΩL`, a fundamental domain for the subgroup of principal ideles $L^\times$ in it. The hypotheses `hΦKs`, `hΦK`, `hΩK` are the exact analogues for `ΦK`, `νZK`, `ΩK` over $K$.
--
--   **Galois and descent data.** `D` is an `IdeleGaloisDescent` for $\mathbb{A}_L$ over $K$, i.e. a continuous action of $\mathrm{Gal}(L/K)$ on $\mathbb{A}_L$ by ring automorphisms compatible with the embedding of $L$; $\sigma$ is an element of $\mathrm{Gal}(L/K)$ which by `hgen` is such that $\sigma^{-1}$ generates the whole group, and by `hdeg` the degree $[L:K]$ is prime.
--
--   **Place sets.** `SK`, `SL` are finite sets of finite places of $K$, resp. $L$, with: `hSL`, every place of $L$ above a place of `SK` lies in `SL`; `hSsat`, membership in `SL` depends only on the place of $K$ below; `hS`, every place of $L$ over a place of $K$ outside `SK` has ramification index $1$.
--
--   **The character $\xi_L$.** `ξL` is a homomorphism from the full idele group of $L$ (as the top subgroup) to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`), takes the same value on $\det \mathrm{heckeGen}(w)$ and $\det \mathrm{heckeGen}(w')$ whenever $w,w'\notin SL$ lie over the same place of $K$ (`hξσ`), and is invariant under the automorphism `D.unitsAct σ.symm` of $\mathbb{A}_L^\times$ (`hξinv`); here `heckeGen` is the adelic matrix $\mathrm{diag}(\varpi_w,1)$ concentrated at $w$.
--
--   **Levels and archimedean types.** `N` is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in `SL` (`hN`), `N'` an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in `SK` (`hN'`); `tysL`, `tysK` are `ArchTypeFamily` data for $L$ and $K$ (for each infinite place a finite list of representations of the row-isometry subgroup at that place).
--
--   **Local test data and matching.** `φa`, `faK` are functions on $\mathrm{GL}_2$ of the infinite adeles of $L$, resp. $K$, and are archimedean test factors (`hφa`, `hfaK`): compactly supported and given by a smooth function of the matrix entries in the mixed space. For each finite place $v$ of $K$, `φS v` is a function on $\mathrm{GL}_2(L\otimes_K K_v)$ and `fSK v` one on $\mathrm{GL}_2(K_v)$; for $v\in SK$ these are locally constant with compact support (`hφS`, `hfSK`). The hypotheses `hmatchA` and `hmatchS` assert matching of orbital integrals: `AreMatchingArch K L σ.symm φa faK` at the archimedean place, and `AreMatchingLocal K L v σ.symm (φS v) (fSK v)` for $v\in SK$, in the sense of `AreMatchingOn` (equality of twisted and ordinary orbital integrals at regular semisimple norms with coupled Haar measures on the centralisers, and vanishing of the orbital integral of the $K$-function at regular semisimple classes that are not norms).
--
--   **A compact box.** `X` is a compact set of functions from the finite places of $L$ to $\mathbb{C}\times\mathbb{C}$ containing (`hX`) all $x$ that vanish on `SL` and satisfy, for $w\notin SL$: $(x\,w)_2 = \mathrm{cNorm}(w)\,\xi_L(\det\mathrm{heckeGen}(w))$ with $\mathrm{cNorm}(w)=\mathrm{absNorm}(w)$, the Ramanujan-type bound $\|(x\,w)_1\|\le(\mathrm{absNorm}(w)+1)\sqrt{\|\xi_L(\det\mathrm{heckeGen}(w))\|}$, and $\overline{(x\,w)_1} = \overline{(x\,w)_2}\,\|(x\,w)_2\|^{-1}(x\,w)_1$.
--
--   **The character set $\Xi$.** `Ξ` is a finite set of characters of the idele group of $K$, characterised by `hΞ` as consisting exactly of those $\xi$ that are continuous, trivial on principal ideles of $K$, and satisfy $\xi\circ(\text{idelic norm of the genuine base change }K\to L)=\xi_L$. By `hur`, every $\xi\in\Xi$ is trivial on the local units of valuation $1$ at each $v\notin SK$, embedded into the ideles by `localUnit` followed by `finIncl`.
--
--   **The geometric comparison.** `c₀` is a complex number and `hgeo` states: for every finite $S'\supseteq SK$ and every pair of functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which are continuous with compact support, are unit-factorisable above $S'$ of type `tysL` for the level $\mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, resp. unit-factorisable at $S'$ of type `tysK` for $\mathrm{principalLevel}(N')\sqcap\ker(\mathrm{glArch})$, satisfy `AreMatchingAt K L σ.symm S' φ f`, and for which at each $v\notin S'$ with unramified fibre the indicator functions of `semiLocalIntegralSet` and `localIntegralSet` match locally, one has
--   $$\int_{\Phi_L}\int_{\Omega_L}\xi_L(z)\sum_{\delta}\varphi\big(x^{-1}\,\delta\,{}^{\sigma^{-1}}(z x)\big) = c_0\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\big(k_{\mathrm{cen}}(x,zx)+k_{\mathrm{ell}}(x,zx)\big),$$
--   where the inner sum on the left is the finsum over those $\delta\in\mathrm{GL}_2(L)$ whose $\sigma^{-1}$-twisted conjugacy class has norm class equal to the conjugacy class of some $\gamma$ in the central or elliptic cell of $\mathrm{GL}_2(K)$, the twisting being by `sigmaAdelicAct K L D σ.symm`, and $k_{\mathrm{cen}},k_{\mathrm{ell}}$ are `adelicKernelCentralPart` and `adelicKernelEllipticPart` of $f$ (finsums of $f(x^{-1}\gamma y)$ over the central, resp. elliptic, cell).
--
--   **Conclusion.** There exists $\lambda\in\mathbb{C}$, $\lambda\neq 0$, with the following two properties.
--
--   (i) If there exist a finite $S'\supseteq SK$ and functions $\varphi$, $f$ satisfying exactly the admissibility list occurring in `hgeo` (continuity, compact support, unit-factorisability of the stated types and levels, `AreMatchingAt K L σ.symm S' φ f`, and the local matching of the indicator functions of the integral sets at the unramified places outside $S'$) for which the $K$-side central-plus-elliptic fold $\sum_{\xi_K\in\Xi}\int_{\Phi_K}\int_{\Omega_K}\xi_K(z)\big(k_{\mathrm{cen}}(x,zx)+k_{\mathrm{ell}}(x,zx)\big)$ is non-zero, then $([L:K]:\mathbb{C})\cdot\lambda = c_0$.
--
--   (ii) For every finite set $T$ of finite places of $K$ disjoint from `SK` (`hTdisj`) with $\#T\ge 2$ (`hT2`) such that no place of $L$ above a place of $T$ lies in `SL` (`hTSL`), and for every choice of: an extension `ws v` of each $v$ to $L$; a map `w'` with $(w'v)$ the ideal $\sigma^{-1}\cdot(\mathrm{ws}\,v)$ for $v\in T$ (`hw'`); elements `ϖs v` of the completion integers at $\mathrm{ws}\,v$, irreducible with non-zero image in the completion for $v\in T$ (`hϖirr`, `hϖs0`); integers `ns v` and families `rTs v` which for $v\in T$ form a Hecke coset system (`hrTs`) for the integral subgroup of $\mathrm{GL}_2$ of the completion at $\mathrm{ws}\,v$ and the element $\mathrm{diag}(\varpi,1)$, i.e. a system of representatives for the left cosets in the double coset; elements `zs v` which for $v\in T$ are the scalar matrices $\varpi\cdot 1$ (`hzs`); the analogous data `ϖKs`, `nKs`, `rKs`, `zKs` over $K$ with `hϖKirr`, `hϖKs0`, `hrKs`, `hzKs`; and complex numbers `s v` with $(s\,v)^2=\xi_L(\det\mathrm{heckeGen}(w'v))$ for $v\in T$ (`hs`) —
--
--   there exists a winding datum $\mathcal{B}$ of shape $r=\#\{\text{infinite places of }K\}$, $d=\#T$, $c=r+\#T$ (a discrete subgroup $\Lambda$ of $\mathbb{R}^r\times\mathbb{Z}^d$ with a linear functional and frequency vector satisfying the pairing relation on $\Lambda$, a character of $\Lambda$ with values in $(\mathbb{R}/\mathbb{Z})^c$, a sequence of subgroups of $\Lambda$, a sequence of continuous integrable functions on $\mathbb{R}^r$ with quadratic decay of themselves and of their Fourier transforms, and the attendant integer, phase, base-point and weight sequences; its coefficients $\mathcal{B}.\mathrm{coeff}(n)$ for $n\in\mathbb{Z}^d$ are the sums $\sum_i \mathrm{lam}_i\,\mathcal{B}.\mathrm{fibreCoeff}_i(n)$) such that the following holds.
--
--   For all exponent functions `ks`, `js` on the finite places of $K$; every continuous compactly supported $\varphi_L$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ such that (`hSLF`) $\varphi_L$ has the semi-local factorisation over $SK\cup T$ with archimedean factor $\varphi_a$, finite factor $\varphi_f$ and semi-local factors equal to $\varphi_S v$ for $v\notin T$ and, for $v\in T$, to the Hecke-word function
--   $$x\mapsto \sum_{\iota:\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)} \mathbf{1}_{\mathrm{semiLocalIntegralSet}}\Big(\big(\mathrm{semiLocalComponent}_v(\mathrm{localEmbed}_{\mathrm{ws}\,v}(\textstyle\prod_m r_{T}(v)(\iota\,m)\cdot (z_s v)^{j_v})\big)^{-1}x\Big),$$
--   which is bi-invariant under $\mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$ (`hbi`) and arch bi-finite of type `tysL` (`harch`); and every family `fam` indexed by functions $m$ assigning to each $v\in T$ an element of $\mathrm{Fin}\,2\to_0\mathbb{N}$, such that (`hfam`) for each $m$ in the Satake slot index set `slotIndex K L ws ks js T` (the `Finset.pi` over $T$ of the supports of the slot words) the function `fam m` is bi-invariant under $\mathrm{principalLevel}(N')\sqcap\ker(\mathrm{glArch})$, arch bi-finite of type `tysK`, `faK` is an archimedean test factor and the `fSK v` ($v\in SK$) are local test functions (these two clauses being restated inside `hfam`), and there is a finite test factor $f_f$ (locally constant, compactly supported) which on matrices with all components integral outside $SK\cup T$ equals the product over $v\in SK\cup T$ of $f_{SK}\,v$ for $v\notin T$ and, for $v\in T$, of the Hecke-word function with word length $(m\,v)_0$ and central power $(m\,v)_1$ built from `rKs v`, `zKs v`, which vanishes whenever some component outside $SK\cup T$ fails to be integral, and which satisfies $\mathrm{fam}\,m\,(g)=f_{aK}(g_\infty)f_f(g_{\mathrm{fin}})$; and such that (`hmatch`) $\varphi_L$ and $x\mapsto\sum_{m}\mathrm{slotFamilyCoeff}(m)\,\mathrm{fam}\,m\,(x)$ match at $SK\cup T$, the slot family coefficient being the product over $v\in T$ of the slot coefficients at $(k_v,j_v,m\,v)$:
--
--   for all $A_L,B_L\in\mathbb{C}$, all families $A_K,B_K$ of complex numbers indexed by characters of the idele group of $K$ and by slot indices, and all $R_0\in\mathbb{R}$, if for every $R\ge R_0$ both truncated integrals are affine in $R$ with these slopes and intercepts, namely
--
--   — the integral over $x$ in `canonicalTruncationDomain L α β` and $z\in\Omega_L$ of $\xi_L(z)$ times the difference of the finsum of $\varphi_L(x^{-1}\delta\,{}^{\sigma^{-1}}(zx))$ over those $\delta\in\mathrm{GL}_2(L)$ whose twisted class has norm class that of some $\gamma$ in the hyperbolic cell of $\mathrm{GL}_2(K)$, and of the indicator of the high set $\{g:\mathrm{adelicHeight}_L(g)>e^R\}$ applied to the constant term at $zx$ — the constant term being the integral, against the conditional measure of the adelic additive Haar measure on `adelicBox L`, of the unipotent translates of the function $y\mapsto$ finsum over $\delta\in\mathrm{GL}_2(L)$ with lower-left entry $0$ and $\mathrm{Norm}_{L/K}(\delta_{00}/\delta_{11})\ne 1$ of $\varphi_L(x^{-1}\delta\,{}^{\sigma^{-1}}y)$ — equals $R\,A_L+B_L$; and
--
--   — for every $\xi_K\in\Xi$ and every slot index $m$, the integral over $x$ in `canonicalTruncationDomain K α β` and $z\in\Omega_K$ of $\xi_K(z)$ times the difference of `adelicKernelHyperbolicPart K (fam m) x (z x)` and the indicator of $\{g:\mathrm{adelicHeight}_K(g)>e^R\}$ applied to the corresponding constant term (unipotent averages over `adelicBox K` of $y\mapsto$ finsum over $\gamma$ with lower-left entry $0$ and $\gamma_{00}/\gamma_{11}\neq 1$ of $\mathrm{fam}\,m\,(x^{-1}\gamma y)$) equals $R\,A_K(\xi_K,m)+B_K(\xi_K,m)$;
--
--   then the intercepts satisfy
--   $$B_L-([L:K]:\mathbb{C})\,\lambda\sum_{\xi_K\in\Xi}\sum_{m}\mathrm{slotFamilyCoeff}(m)\,B_K(\xi_K,m)\;=\;\sum_{n}\Big(\prod_{i}\big(\sqrt{\mathrm{absNorm}(w'v_i)}\,s(v_i)\big)^{k_{v_i}}\,\xi_L\big(\det\mathrm{heckeGen}(w'v_i)\big)^{j_{v_i}}\,\big[(T+T^{-1})^{k_{v_i}}\big]_{n_i}\Big)\,\mathcal{B}.\mathrm{coeff}(n),$$
--   where $i$ runs over $\mathrm{Fin}(\#T)$, $v_i$ is the place of $T$ indexed by $i$ under `T.equivFin`, $n$ runs over the product of the intervals $[-k_{v_i},k_{v_i}]\subset\mathbb{Z}$, and $[\cdot]_{n_i}$ denotes the coefficient in the Laurent polynomial ring over $\mathbb{C}$. The slopes $A_L$ and $A_K$ occur only in the affineness hypothesis; the asserted identity involves the intercepts alone.
--
--   This is the winding-datum form of the comparison of hyperbolic terms in the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$ of prime degree, in the setting of base change for $\mathrm{GL}(2)$: the transfer constant $\lambda$ is produced once and for all, independently of the auxiliary finite set $T$ of Hecke places and of all word and coset data, and the hyperbolic intercepts on the two sides are compared at $[L:K]\lambda$, the difference being expanded in Satake–Laurent coefficients against the coefficients of a winding datum. It is used by the companion statement of the same shape with the archimedean and local matching hypotheses discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_const_forall_exists_windingDatum_hyperbolicIntercept_sub_finrank_mul_const_mul_sum_eq_sum_satakeLaurent_mul_coeff_of_eq_affine_of_areMatchingArch_of_areMatchingLocal
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
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

    (hξinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ.symm z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (hfaK : IsArchTestFactor K faK)
    (hfSK : ∀ v ∈ SK, IsLocalTestFn K v (fSK v))
    (hφa : IsArchTestFactor L φa)
    (hφS : ∀ v ∈ SK, IsSemiLocalTestFn K L v (φS v))
    (hmatchA : AreMatchingArch K L σ.symm φa faK)
    (hmatchS : ∀ v ∈ SK, AreMatchingLocal K L v σ.symm (φS v) (fSK v))
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1) :
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (hTdisj : Disjoint T SK)
      (hT2 : 2 ≤ T.card)
      (hTSL : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
      (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
      (hw' : ∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal)
      (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L)
      (hϖirr : ∀ v ∈ T, Irreducible (ϖs v))
      (hϖs0 : ∀ v ∈ T, algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
      (ns : HeightOneSpectrum (𝓞 K) → ℕ)
      (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
      (hrTs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
        (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v))
      (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (hzs : ∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))
      (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
      (hϖKirr : ∀ v ∈ T, Irreducible (ϖKs v))
      (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
      (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
      (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
      (hrKs : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
      (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
      (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (s : HeightOneSpectrum (𝓞 K) → ℂ)
      (hs : ∀ v ∈ T, s v ^ 2 = ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)),
    ∃ (ℬ : AutomorphicForm.WindingDatum (Fintype.card (NumberField.InfinitePlace K)) T.card
        (Fintype.card (NumberField.InfinitePlace K) + T.card)),
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
      ∀ (AL BL : ℂ) (AK BK : (((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → ℂ))) (R₀ : ℝ),
        (∀ R : ℝ, R₀ ≤ R →
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
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) = (R : ℂ) * AL + BL ∧
          ∀ ξK ∈ Ξ, ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) = (R : ℂ) * AK ξK m + BK ξK m) →
      (BL - (Module.finrank K L : ℂ) * lam * ∑ ξK ∈ Ξ, ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
            SatakeCombination.slotFamilyCoeff K L ws ks js T m * BK ξK m =
          ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff (n i)) * ℬ.coeff n) := by sorry
