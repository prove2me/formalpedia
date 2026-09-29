-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram
-- name    : AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9ff26600-eb98-5ee3-864b-6d7c3e95975f
-- title:
--   Truncated unipotent term as rank-one Tate integrals over K
-- statement:
--   **Data.** Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\alpha, \beta$ be reals with $0 < \alpha$ and $\alpha < \beta$. Fix a set $\Phi_L$ of points of $\mathrm{GL}_2(\mathbb{A}_L)$ (it enters through the record `productionPinsOf` below), a Haar measure $\nu_{Z,L}$ on the idèle group $(\mathbb{A}_L)^\times$ and a set $\Omega_L$ which, by `hΩL`, is a fundamental domain for the action of the image of $L^\times$ under `Units.map (algebraMap L (AdeleRing (𝓞 L) L))` on $(\mathbb{A}_L)^\times$ with respect to $\nu_{Z,L}$. Fix a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$ which is compatible with $L \to \mathbb{A}_L$ and continuous for each $\tau$, an element $\sigma \in \mathrm{Gal}(L/K)$, and the hypothesis `hgen` that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. Fix a finite set $S_L$ of primes of $\mathcal{O}_L$ subject to `hSL`: every $w$ whose ramification index over the prime of $\mathcal{O}_K$ below it differs from $1$ belongs to $S_L$. Fix a homomorphism $\xi_L$ from the full subgroup $\top \le (\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, with the central-character hypotheses `hξc` (the associated $\mathbb{C}$-valued function $z \mapsto \xi_L(z)$ is continuous) and `hξt` ($\xi_L$ is trivial on the image of $L^\times$). Fix a finite set $S$ of primes of $\mathcal{O}_K$, a function $\varphi_a$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$, and a family $\varphi_S$ of functions on $\mathrm{GL}_2(L \otimes_K K_v)$, one for each finite place $v$ of $K$.
--
--   **Siegel and fundamental-domain data on the $L$ side.** Reals $c, u, d_1, d_2$ with $0 < c$, a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ and a set $\Phi_0$ satisfying three conditions: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂`, namely the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c \le$ `localHeight` and `xWindowSq` $\le u^2$ at every infinite place, and whose archimedean determinant norms lie in $[d_1, d_2]$ at every infinite place; `hΦ₀s`, that on $\Phi_0$ the idèle norm of $\det g$ lies in $[\alpha,\beta]$; and `hΦ₀`, that $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to $\{g : |\det g| \in [\alpha,\beta]\}$.
--
--   **Measure data on the $K$ side.** An additive Haar measure $\mu_K$ on $\mathbb{A}_K$ normalised by `hμK1` so that the adelic box `AdelicBox.adelicBox K` has mass $1$; a Haar measure $\nu_K$ on $(\mathbb{A}_K)^\times$ together with a set $\Omega_K$ which by `hΩK` is a fundamental domain for the image of $K^\times$; and for each finite place $v$ of $K$ an additive Haar measure $\mu_f\,v$ on $K_v$. Measurability and Borel-space assumptions for the idèle and adèle groups of $K$ and $L$ and for the completions $K_v$ are grouped with these.
--
--   **Conclusion.** For every finite set $T$ of primes of $\mathcal{O}_K$ such that no prime of $\mathcal{O}_L$ lying over a member of $T$ belongs to $S_L$; for every choice $w_v := (\mathrm{ws}\,v)$ of an extension of each $v$ to $L$ and every map $w'$ from primes of $\mathcal{O}_K$ to primes of $\mathcal{O}_L$ with $(w'\,v)$ equal to the $\sigma$-translate of the ideal of $w_v$ for $v \in T$; for every family $\varpi_v$ of elements of the valuation ring of $L_{w_v}$ which are irreducible for $v \in T$, together with the hypothesis $h_{\varpi,0}$ that their images in $L_{w_v}$ are nonzero for $v \in T$; for every family of naturals $n_v$ and families $r_{T,v} : \mathrm{Fin}(n_v) \to \mathrm{GL}_2(L_{w_v})$ such that for $v \in T$ the system $r_{T,v}$ is a Hecke coset system (`IsHeckeCosetSystem`) for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) — the image of $\mathrm{GL}_2(\mathcal{O}_{w_v})$ in $\mathrm{GL}_2(L_{w_v})$ — and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $= \mathrm{diag}(\varpi_v, 1)$, that is: each representative lies in the double coset $U\,g\,U$, every element of $U\,g\,U$ lies in $r_{T,v}(i)\,U$ for some $i$, and the cosets $r_{T,v}(i)\,U$ are pairwise distinct; and for every family $z_v \in \mathrm{GL}_2(L_{w_v})$ whose underlying matrix for $v \in T$ is the scalar matrix $\varpi_v \cdot 1$ — there exist $n \in \mathbb{N}$, weights $\kappa_w : \mathrm{Fin}\,n \to \mathbb{C}$, thresholds $a : \mathrm{Fin}\,n \to \mathbb{R}$, a real $b$, a finite set $S_x$ of primes of $\mathcal{O}_K$, archimedean factors $g_j : \mathbb{A}_{K,\infty} \to \mathbb{C}$ and auxiliary local factors $h_{0,j,v} : K_v \to \mathbb{C}$ such that the following hold.
--
--   (i) $0 < a_j$ for every $j$; (ii) $b \ne 0$; (iii) $S \cup T \subseteq S_x$.
--
--   (iv) For all families of naturals $(k_v)_v$, $(j_v)_v$ and every $j$, the function
--   $$\Psi_j(x) \;=\; \mathbf{1}_{\mathrm{integralOutside}(S_x)}(x)\cdot g_j(x_\infty)\prod_{v \in S_x} F_{j,v}(x_v),\qquad F_{j,v} = \begin{cases} \mathrm{twistedLocalFactor}\,K\,L\,D\,\sigma\,\xi_L\,v\,w_v\,n_v\,r_{T,v}\,z_v\,k_v\,j_v, & v \in T,\\ h_{0,j,v}, & v \notin T,\end{cases}$$
--   lies in the Schwartz–Bruhat space [`NumberField.AdelicFourier.schwartzBruhat K`](def/NumberField_AdelicFourier.html#L80) and has compact support; here `integralOutside` $S_x$ is the set of adèles whose $v$-component is integral for all $v \notin S_x$, and [`twistedLocalFactor`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) is the local trace pushforward to $K_v$ of the semi-local twisted orbital function [`TwistedUnipotentTerm.unipotentOrbitalFn`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L57) attached to the data $\xi_L, w_v, r_{T,v}, z_v, k_v, j_v$.
--
--   (v) For all families $(k_v)_v$, $(j_v)_v$, every $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and every $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{L,f})$ such that `IsSemiLocalFactorization K L (S ∪ T)` holds for $\varphi, \varphi_a, \varphi_f$ and the semi-local family which at $v \in T$ is
--   $$x \;\longmapsto\; \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\mathrm{semiLocalIntegralSet}}\Bigl(\bigl(\mathrm{semiLocalComponent}_v\bigl(\mathrm{localEmbed}_{w_v}\bigl(\textstyle\prod_m r_{T,v}(\iota(m)) \cdot z_v^{\,j_v}\bigr)\bigr)\bigr)^{-1} x\Bigr)$$
--   and at $v \notin T$ is $\varphi_S\,v$ — that is: $\varphi_a$ is an archimedean test factor, $\varphi_f$ is locally constant with compact support, each member of the family at a place of $S \cup T$ is locally constant with compact support, $\varphi_f(h)$ equals the product over $v \in S \cup T$ of the family members at the semi-local components of $h$ whenever all components outside $S \cup T$ are integral, $\varphi_f(h) = 0$ when some component outside $S \cup T$ is not integral, and $\varphi(g) = \varphi_a(\mathrm{glArch}\,g)\,\varphi_f(\mathrm{glFin}\,g)$ — there exists $R_0 \in \mathbb{R}$ such that for every $R \ge R_0$ the three following assertions hold, with
--   $$\mathcal{K}_R(x,z) \;=\; \sum^{\mathrm{f}}_{\delta} \varphi\bigl(x^{-1}\,\iota(\delta)\, \mathrm{sigmaAdelicAct}_{\sigma}(\mathrm{centralScalar}(z)\,x)\bigr) \;-\; \mathbf{1}_{\{\,\exp R \,<\, \mathrm{adelicHeight}_L\,\}}\cdot \mathrm{CT}(x)\quad\text{evaluated at } \mathrm{centralScalar}(z)\,x ,$$
--   where the first finite sum runs over those $\delta \in \mathrm{GL}_2(L)$ for which there is a $\gamma$ in the unipotent cell of $\mathrm{GL}_2(K)$ — the set of $\gamma$ whose matrix is not of central type and has characteristic polynomial $(X - a)^2$ for some $a$ — with [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the $\sigma$-twisted class of $\delta$ equal to the conjugacy class of $\gamma$, $\iota$ denotes `globalPoints`, and $\mathrm{CT}$ is the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) taken with respect to the measurable space and measure of the record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)` — i.e. the Borel structure on $\mathbb{A}_L$ and the additive Haar measure conditioned on the adelic box — along the unipotent family $t \mapsto \mathrm{unipotentGL2}(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$, applied to the function
--   $$y \;\longmapsto\; \sum^{\mathrm{f}}_{\delta \,:\, \delta_{10} = 0,\; N_{L/K}(\delta_{00}/\delta_{11}) = 1} \varphi\bigl(x^{-1}\,\iota(\delta)\,\mathrm{sigmaAdelicAct}_{\sigma}(y)\bigr).$$
--
--   The three assertions are: first, for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ the function $z \mapsto \xi_L(z)\,\mathcal{K}_R(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$; second, the function $x \mapsto \int_{\Omega_L} \xi_L(z)\,\mathcal{K}_R(x,z)\,d\nu_{Z,L}$ is integrable on $\Phi_0$ with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`; and third, the identity
--   $$\int_{\Phi_0}\!\int_{\Omega_L} \xi_L(z)\,\mathcal{K}_R(x,z)\,d\nu_{Z,L}\,d\,\mathrm{adelicGLHaar} \;=\; \sum_{j} \kappa_w(j) \int_{\Omega_K} |y|^{-1}\Bigl( \sum^{\mathrm{f}}_{\eta \in K^\times} \Psi_j\bigl(\eta\, y^{-1}\bigr) \;-\; \begin{cases} |y| \displaystyle\int \Psi_j \, d\mu_K, & a_j\,e^{bR} < |y|,\\ 0, & \text{otherwise}\end{cases} \Bigr) d\nu_K ,$$
--   where $|y|$ denotes the idèle norm [`NumberField.TateGlobal.ideleNorm K y`](def/NumberField_TateGlobalZeta.html#L19), $\eta$ is mapped into $\mathbb{A}_K$ by `algebraMap`, and $\Psi_j$ is the function of (iv) formed from the same $(k_v)_v$, $(j_v)_v$.
--
--   This is the unipotent-type contribution to the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, in the unramified Hecke-word situation: the truncated twisted kernel, averaged against the central character $\xi_L$ over a fundamental domain and integrated over $\Phi_0$, is expressed as a finite linear combination of truncated rank-one Tate integrals over $K$ of explicit factorisable Schwartz–Bruhat functions whose components at the places of $T$ are the twisted local factors. It feeds the comparison in which these rank-one integrals are evaluated in terms of local zeta integrals, namely [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_mul_localZeta_twistedLocalFactor_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram.lean

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
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox

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
    AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νK : Measure (AdeleRing (𝓞 K) K)ˣ) [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)) [∀ v, (μf v).IsAddHaarMeasure] :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
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
            ∃ (n : ℕ) (κw : Fin n → ℂ) (a : Fin n → ℝ) (b : ℝ) (Sx : Finset (HeightOneSpectrum (𝓞 K)))
        (g : Fin n → InfiniteAdeleRing K → ℂ)
        (h₀ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ),
        (∀ j, 0 < a j) ∧ b ≠ 0 ∧ S ∪ T ⊆ Sx ∧
      (∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (j : Fin n),
        ((fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) ∈ NumberField.AdelicFourier.schwartzBruhat K ∧
          HasCompactSupport (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x))) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
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
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
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
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
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
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ∑ j : Fin n, κw j * ∫ y in ΩK,
          ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
            ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)
                (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
              (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) ∂νK := by sorry
