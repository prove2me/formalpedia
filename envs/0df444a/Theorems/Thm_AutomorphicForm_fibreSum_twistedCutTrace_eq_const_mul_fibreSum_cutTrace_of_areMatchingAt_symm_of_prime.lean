-- Prove2me | Theorems.Thm_AutomorphicForm_fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime
-- name    : AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f68ad317-f1a7-5ed8-ac58-92bf18ce121b
-- title:
--   Fibrewise twisted trace comparison at prime degree
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, and `hdeg` requires the degree $[L:K] = \operatorname{finrank}_K L$ to be a prime number. Both `AdelicGL2 (𝓞 K) K` and `AdelicGL2 (𝓞 L) L` denote $\mathrm{GL}_2$ of the adele ring of the corresponding field.
--
--   **Geometric data over $K$ (`cK`, `uK`, `d₁K`, `d₂K`, `TK`, `hcK`, `hd₁K`, `hdK`, `hcovK`).** Real numbers $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$ and $0 < d_{1K} < d_{2K}$ are given, together with a finite set $T_K$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$. The hypothesis `hcovK` asserts `CoversModCentre K` for the union $\bigcup_{x \in T_K} (\,\cdot\, x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}]$ of right translates of the centre-cut Siegel window, i.e. for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ there are $\gamma \in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\,g\,z$ (the image of $\gamma$ under `globalPoints`, times $g$, times the central scalar attached to $z$) in that union. The window `centreCutSiegelSet` consists of those $g$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ satisfies $c_K \le$ `localHeight`, `xWindowSq` $\le u_K^2$, and `archDetNorm` $\in [d_{1K}, d_{2K}]$.
--
--   **Geometric data over $L$ (`α`, `β`, `hα`, `hαβ`, `ΦL`, `hΦs`, `hΦ`).** Reals $0 < \alpha < \beta$ are given and a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ contained in the determinant slab $\{g : \mathrm{ideleNorm}\,L(\det g) \in [\alpha,\beta]\}$ (`hΦs`), which by `hΦ` is a fundamental domain for the translation action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` on the adelic Haar measure `adelicGLHaar` restricted to that slab.
--
--   **Twisting data (`D`, `σ`, `hσ`).** $D$ is an `IdeleGaloisDescent` for $\mathcal{O}_L$ over $K, L$: a homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous in each automorphism. Further, $\sigma$ is a $K$-automorphism of $L$ with $\sigma \neq 1$.
--
--   **Sets of primes (`SK`, `SL`, `hSL`, `hSsat`, `hS`).** $S_K$ and $S_L$ are finite sets of height-one primes of $\mathcal{O}_K$ and $\mathcal{O}_L$. Every prime of $L$ lying over a prime in $S_K$ lies in $S_L$ (`hSL`); $S_L$ is a union of fibres, in that two primes of $L$ with the same image in $\mathrm{Spec}\,\mathcal{O}_K$ are simultaneously in or out of $S_L$ (`hSsat`); and every prime $w$ of $L$ whose image is outside $S_K$ has ramification index $1$ over that image (`hS`).
--
--   **Characters (`ξL`, `hξc`, `hξt`, `hξσ`, `Ξ`, `hΞ`).** $\xi_L$ is a homomorphism from the full subgroup $\top$ of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $L^\times$ (`hξt`), and taking the same value on $\det(\mathrm{heckeGen}\,w)$ and $\det(\mathrm{heckeGen}\,w')$ whenever $w, w' \notin S_L$ lie over the same prime of $K$ (`hξσ`). $\Xi$ is a finite set of homomorphisms from $\top \le \mathbb{A}_K^\times$ to $\mathbb{C}^\times$, characterised by `hΞ`: $\xi \in \Xi$ precisely when $\xi$ is continuous, trivial on the image of $K^\times$, and satisfies $\xi(\mathrm{N}(z)) = \xi_L(z)$ for all $z \in \mathbb{A}_L^\times$, where $\mathrm{N}$ is the idelic norm `idelicNorm` of the base change `genuineBaseChange K L`.
--
--   **Levels, types and test functions (`N`, `hN`, `tysL`, `φ`, `hφ`, `hφc`, `hφt`, `N'`, `hN'`, `tysK`, `f`, `hf`, `hfc`, `hft`).** $N$ is an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`), $\mathrm{tys}_L$ an archimedean type family for $L$, and $\varphi$ a continuous, compactly supported complex function on $\mathrm{GL}_2(\mathbb{A}_L)$ which by `hφt` is unit-factorizable above $K$ of type $\mathrm{tys}_L$ for the subgroup $\mathrm{levelOne}\,N \sqcap \mathrm{finiteAdelicGL2Subgroup}\,L$ and the set $S_K$: it is bi-invariant under that subgroup, factors as $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$ with an archimedean test factor, a finite test factor, and semi-local test functions $\varphi_{S}(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for $v \in S_K$ such that $\varphi_f$ is the product of the $\varphi_S(v)$, $v\in S_K$, on finite matrices all of whose semi-local components outside $S_K$ are integral and vanishes otherwise; and $\varphi$ is archimedean bi-finite of type $\mathrm{tys}_L$. Symmetrically, $N'$ is an ideal of $\mathcal{O}_K$ with all prime divisors in $S_K$ (`hN'`), $\mathrm{tys}_K$ an archimedean type family for $K$, and $f$ a continuous, compactly supported complex function on $\mathrm{GL}_2(\mathbb{A}_K)$ which by `hft` is unit-factorizable of type $\mathrm{tys}_K$ for $\mathrm{principalLevel}\,N' \sqcap \mathrm{finiteAdelicGL2Subgroup}\,K$ and $S_K$ (the analogous bi-invariance, factorisation with local test functions at the places of $S_K$, and archimedean bi-finiteness).
--
--   **Matching (`hm`).** `AreMatchingAt K L σ.symm SK φ f` holds: there are factorisations of $\varphi$ and $f$ as above whose archimedean factors match and whose factors at each $v \in S_K$ match, matching being understood with respect to $\sigma^{-1}$ in the sense of `AreMatchingOn`: twisted orbital integrals of the $L$-side function at a $\delta$ with regular semisimple norm string agree with orbital integrals of the $K$-side function at any regular semisimple $\gamma$ admitting a norm conjugator $y$ for $\delta$, for coupled Haar measures on the centraliser and the twisted centraliser, and orbital integrals of the $K$-side function vanish at regular semisimple classes which are not norms.
--
--   **Fundamental-lemma hypotheses (`hFLu`, `hFLs`, `hFLi`).** For each prime $v \notin S_K$ these assert matching, with respect to $\sigma^{-1}$, of prescribed pairs of local functions. `hFLu`: if every prime of $L$ over $v$ is unramified, the indicator of the semi-local integral set `semiLocalIntegralSet K L v` matches the indicator of `localIntegralSet K v`. `hFLs` (split case): for every $K_v$-algebra isomorphism $e : L \otimes_K K_v \cong K_v^{[L:K]}$, every index $i_0$, every subgroup $U$ equal to the integral subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) of $\mathrm{GL}_2(K_v)$, and every element $f_1$ of the Hecke algebra of $U$, the function $g \mapsto f_1(e(g)_{i_0})$ times the indicator of the set of $g$ whose remaining components lie in $U$ matches $f_1$. `hFLi` (inert case): for every prime $w$ of $L$ over $v$ with ramification index $1$, every isomorphism $e : L \otimes_K K_v \cong L_w$ over $K_v$, irreducible uniformisers $\varpi_K$, $\varpi_L$ with nonzero images in $K_v$, $L_w$, the integral subgroups $U_K \le \mathrm{GL}_2(K_v)$ and $U_L \le \mathrm{GL}_2(L_w)$, Hecke-algebra elements given as the indicator of the double coset of [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) of the respective uniformiser (the operators $T$) and as $\#(\mathcal{O}_K/v)$, respectively $\#(\mathcal{O}_L/w)$, times the indicator of the set of matrices of the form $\varpi \cdot u$ with $u$ in the integral subgroup (the operators $E$), and any sequence $p$ in the Hecke algebra of $U_K$ with $p_0 = 2$, $p_1 = T_K$ and $p_{k+2} = T_K p_{k+1} - E_K p_k$: there exists a $\mathbb{C}$-algebra homomorphism $b$ from the Hecke algebra of $U_L$ to that of $U_K$ with $b(T_L) = p_{[L:K]}$, $b(E_L) = E_K^{[L:K]}$, and such that for every element $\phi$ of the Hecke algebra of $U_L$ the function $g \mapsto \phi(e(g))$ matches $b(\phi)$.
--
--   **Conclusion.** There exists a complex number $c \neq 0$ such that for every function $t$ from the height-one primes of $\mathcal{O}_L$ to $\mathbb{C} \times \mathbb{C}$ subject to the two conditions
--
--   (i) *(non-Eisenstein)* for every nonzero ideal $M$ of $\mathcal{O}_L$ and every pair of homomorphisms $\chi_1, \chi_2 : \mathbb{A}_L^\times \to \mathbb{C}^\times$ that are continuous and trivial on the image of $L^\times$, there is a prime $w \notin S_L$ with $t(w)$ different from the pair of $w$-th entries $(a_w, b_w)$ of [`LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂`](def/LanglandsTunnell_ConverseData.html#L132), whose entries at $w$ are $\chi_1(\varpi_w) + \chi_2(\varpi_w)$ and $\chi_1(\varpi_w)\chi_2(\varpi_w)$ for the uniformiser idele at $w$; and
--
--   (ii) *(fibrewise constancy)* $t(w) = t(w')$ whenever $w, w' \notin S_L$ lie over the same prime of $K$,
--
--   the following identity of unconditional sums holds. On the left, $\Psi$ ranges over the Hecke eigensystems over $L$ with complex coefficients that belong to `cuspClasses L` for the pins `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L) (adelicBox L)`, the character $\xi_L$, the level $N$ and the set $S_L$ — that is, $\Psi$ has level $N$, vanishing parameters $\Psi.a\,w = \Psi.b\,w = 0$ at all $w \in S_L$, and nonzero isotypic cusp submodule — and which satisfy $(\Psi.a\,w, \Psi.b\,w) = t(w)$ for all $w \notin S_L$; the summand is `twistedCutTrace K L D σ` of those pins, $\xi_L$, $N$, $S_L$, $\Psi$, $\mathrm{tys}_L$ and $\varphi$, namely the trace of the twisted convolution operator attached to $D$, $\sigma$ and $\varphi$ on the intersection of the isotypic cusp submodule of $\Psi$ with the archimedean cut submodule of type $\mathrm{tys}_L$ (and $0$ if that operator does not preserve the submodule). The sum over $\Psi$ equals $c$ times the finite sum over $\xi_K \in \Xi$ of the unconditional sum over those Hecke eigensystems $\pi$ over $K$ with complex coefficients that belong to `cuspClasses K` for the pins `productionPinsOf K` of the union of Siegel translates above, the level subgroups $M \mapsto \mathrm{principalLevel}\,M \sqcap \mathrm{finiteAdelicGL2Subgroup}\,K$, the generators `heckeGen (𝓞 K) K` and `adelicBox K`, the character $\xi_K$, the level $N'$ and the set $S_K$, and which satisfy $((\mathrm{formalBaseChange}\,K\,L\,\pi).a\,w, (\mathrm{formalBaseChange}\,K\,L\,\pi).b\,w) = t(w)$ for all $w \notin S_L$ — the formal base change having, at a prime $\mathfrak{P}$ of $L$ over $v$, first parameter the Satake power `satakePow` of index the inertia degree of $\mathfrak{P}$ over $v$ applied to $(\pi.a\,v, \pi.b\,v)$ and second parameter $(\pi.b\,v)$ raised to that inertia degree — the summand being `cutTrace K` of those pins, $\xi_K$, $N'$, $S_K$, $\pi$, $\mathrm{tys}_K$ and $f$, the trace of convolution by $f$ on the intersection of the isotypic cusp submodule of $\pi$ with the archimedean cut submodule of type $\mathrm{tys}_K$. The constant $c$ is independent of $t$.
--
--   This is the global spectral side of the comparison of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L$ with the ordinary trace formula over $K$ for a cyclic extension of prime degree: after fixing a system $t$ of Hecke parameters outside $S_L$ which is fibrewise constant and not of Eisenstein type, the sum of twisted cut traces over the cuspidal classes over $L$ with parameters $t$ is a fixed nonzero multiple of the sum of cut traces over the cuspidal classes over $K$ whose formal base change has parameters $t$. It is the step from which the existence of a base-change lift is extracted in [`AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime`](thm.html#AutomorphicForm.exists_mem_cuspClasses_principalLevel_of_twistedCutTrace_ne_zero_of_areMatchingAt_inv_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_areMatchingAt_symm_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
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
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f)
    (hm : AreMatchingAt K L σ.symm SK φ f)
    (hFLu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      (∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
        Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1) →
      AreMatchingLocal K L v σ.symm ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
        ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))
    (hFLs : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K]
          (Fin (Module.finrank K L) → v.adicCompletion K))
        (i₀ : Fin (Module.finrank K L)) (U : Subgroup (GL (Fin 2) (v.adicCompletion K))),
        U = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ f₁ : HeckePair.HeckeAlgebra U ℂ,
          AreMatchingLocal K L v σ.symm
            (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ)
                  (Matrix.GeneralLinearGroup.map
                    ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i₀).comp
                      e.toAlgHom).toRingHom g) *
                ({h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) |
                    ∀ i : Fin (Module.finrank K L), i ≠ i₀ →
                      Matrix.GeneralLinearGroup.map
                          ((Pi.evalAlgHom (v.adicCompletion K) (fun _ => v.adicCompletion K) i).comp
                            e.toAlgHom).toRingHom h ∈ U}.indicator (fun _ => (1 : ℂ)) g))
            (f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hFLi : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → ∀ (w : v.Extension (𝓞 L)),
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1 →
      ∀ (e : (L ⊗[K] v.adicCompletion K) ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
        (ϖK : v.adicCompletionIntegers K), Irreducible ϖK →
        ∀ (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
          (ϖL : w.1.adicCompletionIntegers L), Irreducible ϖL →
        ∀ (hϖL0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL ≠ 0)
          (UK : Subgroup (GL (Fin 2) (v.adicCompletion K))),
          UK = LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) →
        ∀ (UL : Subgroup (GL (Fin 2) (w.1.adicCompletion L))),
          UL = LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) →
        ∀ (TK EK : HeckePair.HeckeAlgebra UK ℂ),
          (TK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (HeckePair.doubleCoset UK (LocalGL2.diagPi ϖK hϖK0)).indicator (fun _ => (1 : ℂ)) →
          (EK : GL (Fin 2) (v.adicCompletion K) → ℂ) =
            (Ideal.absNorm v.asIdeal : ℂ) •
              ({x : GL (Fin 2) (v.adicCompletion K) | ∃ u ∈ UK,
                  (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
                    algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
                      (u : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (TL EL : HeckePair.HeckeAlgebra UL ℂ),
          (TL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (HeckePair.doubleCoset UL (LocalGL2.diagPi ϖL hϖL0)).indicator (fun _ => (1 : ℂ)) →
          (EL : GL (Fin 2) (w.1.adicCompletion L) → ℂ) =
            (Ideal.absNorm w.1.asIdeal : ℂ) •
              ({x : GL (Fin 2) (w.1.adicCompletion L) | ∃ u ∈ UL,
                  (x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
                    algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖL •
                      (u : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L))}.indicator
                fun _ => (1 : ℂ)) →
        ∀ (p : ℕ → HeckePair.HeckeAlgebra UK ℂ), p 0 = 2 → p 1 = TK →
          (∀ k : ℕ, p (k + 2) = TK * p (k + 1) - EK * p k) →
          ∃ b : HeckePair.HeckeAlgebra UL ℂ →ₐ[ℂ] HeckePair.HeckeAlgebra UK ℂ,
            b TL = p (Module.finrank K L) ∧ b EL = EK ^ Module.finrank K L ∧
              ∀ φ : HeckePair.HeckeAlgebra UL ℂ,
                AreMatchingLocal K L v σ.symm
                  (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
                    (φ : GL (Fin 2) (w.1.adicCompletion L) → ℂ)
                      (Matrix.GeneralLinearGroup.map e.toAlgHom.toRingHom g))
                  (b φ : GL (Fin 2) (v.adicCompletion K) → ℂ)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ t : HeightOneSpectrum (𝓞 L) → ℂ × ℂ,
        (∀ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
            (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) →
            (∀ z : (AdeleRing (𝓞 L) L)ˣ,
              z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                χ₁ z = 1) →
            (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) →
            (∀ z : (AdeleRing (𝓞 L) L)ˣ,
              z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                χ₂ z = 1) →
            ∃ w : HeightOneSpectrum (𝓞 L), w ∉ SL ∧
              t w ≠ ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
                (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) →
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
            HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → t w = t w') →
        (∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
            Ψ ∈ cuspClasses L
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
              ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → (Ψ.a w, Ψ.b w) = t w},
          twistedCutTrace K L D σ
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc) =
          c * ∑ ξK ∈ Ξ, ∑' π : {π : HeckeEigensystem K ℂ //
              π ∈ cuspClasses K
                (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                  (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK ∧
                ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
                  ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) = t w},
            cutTrace K
              (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π.1 tysK f hf hfc := by sorry
