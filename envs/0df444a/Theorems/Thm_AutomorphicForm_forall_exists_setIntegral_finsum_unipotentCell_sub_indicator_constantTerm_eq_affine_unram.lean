-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram
-- name    : AutomorphicForm.forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/af79fa01-4723-5373-956f-33f213546877
-- title:
--   Affineness in R of the truncated twisted unipotent term
-- statement:
--   Setting. $K \subseteq L$ is a Galois extension of number fields, $\alpha,\beta$ are reals with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`), and $\Phi_L$ is a subset of $\mathrm{GL}_2(\mathbb{A}_L)$. The idele group $(\mathbb{A}_L)^\times$ carries a measurable structure with the Borel property and a Haar measure $\nu_{Z,L}$, and $\Omega_L \subseteq (\mathbb{A}_L)^\times$ is, by `hΩL`, a fundamental domain for the subgroup of principal ideles (the range of $L^\times \to (\mathbb{A}_L)^\times$) with respect to $\nu_{Z,L}$. Further, $D$ is a datum [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ whose value at each $\tau$ is continuous and restricts on $L$ to $\tau$; $\sigma \in \mathrm{Gal}(L/K)$ satisfies `hgen`, that every $\tau$ lies in the subgroup of integer powers of $\sigma$. A finite set $S_L$ of finite places of $L$ is given which, by `hSL`, contains every $w$ whose ramification index `ramificationIdx'` over the place of $K$ below it is not $1$. A homomorphism $\xi_L$ from the top subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ is given, with `hξc` the continuity of $z \mapsto \xi_L(z)$ as a complex-valued function and `hξt` its triviality on principal ideles. Finally $S$ is a finite set of finite places of $K$, $\varphi_a$ a complex-valued function on $\mathrm{GL}_2$ of the infinite adeles of $L$, and $\varphi_S$ a family of complex-valued functions on $\mathrm{GL}_2(L \otimes_K K_v)$, one for each finite place $v$ of $K$.
--
--   The coefficient space. $X$ is a set of "tables" $x$, functions from the finite places of $L$ to $\mathbb{C} \times \mathbb{C}$, and `hX` requires $X$ to contain every table $x$ such that $x(w) = 0$ for all $w \in S_L$ and such that for $w \notin S_L$, writing $g_w =$ `heckeGen (𝓞 L) L w` and $N(w) = \mathrm{absNorm}(w)$: $(x(w))_2 = N(w)\,\xi_L(\det g_w)$ (with $N(w)$ read in $\mathbb{C}$ via `HeckeEigensystem.cNorm`), $\lVert (x(w))_1 \rVert \le (N(w)+1)\sqrt{\lVert \xi_L(\det g_w)\rVert}$, and $\overline{(x(w))_1} = \bigl(\overline{(x(w))_2}/\lVert (x(w))_2 \rVert\bigr)\,(x(w))_1$.
--
--   The fundamental domain. Real numbers $c,u,d_1,d_2$ are given with $0<c$ (`hc`), $T_c$ is a compact subset of $\mathrm{GL}_2(\mathbb{A}_L)$ (`hTc`), and $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ satisfies three hypotheses: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (the set of $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, with $c \le \mathrm{localHeight}$ of every archimedean component, $\mathrm{xWindowSq} \le u^2$ at every archimedean component, and `archDetNorm` at every infinite place lying in $[d_1,d_2]$); `hΦ₀s`, that the idele norm of $\det g$ lies in $[\alpha,\beta]$ for every $g \in \Phi_0$; and `hΦ₀`, that $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure `adelicGLHaar` restricted to $\{g : \lvert\det g\rvert_{\mathbb{A}} \in [\alpha,\beta]\}$.
--
--   Hecke data (quantified in the conclusion). The assertion is made for every finite set $T$ of finite places of $K$ with $2 \le \#T$ such that no place $w$ of $L$ above a place $v \in T$ lies in $S_L$; every family $ws$ assigning to each finite place $v$ of $K$ a place of $L$ above $v$; every map $w'$ from finite places of $K$ to finite places of $L$ with $(w'v)$ the ideal $\sigma \cdot (ws\,v)$ for $v \in T$; every family $\varpi_s$ of elements of the valuation rings $\mathcal{O}_{(ws\,v)}$ which are irreducible for $v \in T$, together with the hypothesis $h\varpi_s0$ that their images in the completions are nonzero for $v \in T$; every $ns$ and every family $rT_s$ of tuples $rT_s\,v : \mathrm{Fin}(ns\,v) \to \mathrm{GL}_2((ws\,v)\text{-completion of } L)$ such that, for $v \in T$, $rT_s\,v$ is a Hecke coset system (`IsHeckeCosetSystem`) for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) and the element [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68) $(\varpi_s v) = \mathrm{diag}(\varpi_s v, 1)$: each representative lies in the double coset $U\,\mathrm{diag}(\varpi_s v,1)\,U$, every element of that double coset is congruent modulo $U$ to one of them, and the induced map to $G/U$ is injective; and every family $z_s$ with $z_s v$ the scalar matrix $\varpi_s v \cdot 1$ for $v \in T$.
--
--   Conclusion. Under these hypotheses there exist continuous $\mathbb{C}$-linear functionals $\mu, \nu$ on $C(X,\mathbb{C})$ — chosen before, hence independently of, the Hecke exponents and test functions quantified below — with the following two properties.
--
--   First, $\mu$ has small mass on functions concentrated near a prescribed point: for every $\tau$ from the finite places of $K$ to $\mathbb{C}\times\mathbb{C}$ and every $\varepsilon>0$ there is a family $U$ of subsets of $\mathbb{C}\times\mathbb{C}$ with $U v$ open and containing $\tau v$ for each $v \in T$, such that every $g \in C(X,\mathbb{C})$ which vanishes at each $y \in X$ for which some $v \in T$ has $y(w'v) \notin U v$, and which satisfies $\lVert g(y)\rVert \le 1$ for all $y$, has $\lVert \mu(g)\rVert < \varepsilon$.
--
--   Second, for all families of exponents $ks, js$ from the finite places of $K$ to $\mathbb{N}$ and all functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ satisfying `IsSemiLocalFactorization K L (S ∪ T)` for $\varphi, \varphi_a, \varphi_f$ and the family of local factors which at $v \in T$ is the Hecke-word indicator sum
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(ks\,v) \to \mathrm{Fin}(ns\,v)} \mathbf{1}_{\text{semiLocalIntegralSet}}\Bigl( \bigl(\text{semiLocalComponent}_v(\text{localEmbed}_{(ws\,v)}(\textstyle\prod_m rT_s v(\iota\,m) \cdot (z_s v)^{js\,v}))\bigr)^{-1} x \Bigr)$$
--   and at $v \notin T$ is $\varphi_S v$ — the factorization condition asserting that $\varphi_a$ is an archimedean test factor, $\varphi_f$ is locally constant with compact support, each local factor at a place of $S \cup T$ is locally constant with compact support, $\varphi_f(h)$ equals the product of the local factors on the semi-local components when all components away from $S \cup T$ are integral and $0$ when some such component is not, and $\varphi(g) = \varphi_a(\text{arch } g)\,\varphi_f(\text{fin } g)$ — there exists $R_0 \in \mathbb{R}$ such that for every $R \ge R_0$ and every $g \in C(X,\mathbb{C})$ given by the monomial
--   $$g(x) = \prod_{v \in T} \bigl(x(w'v)\bigr)_1^{ks\,v}\,\bigl(N(w'v)^{-1}\,(x(w'v))_2\bigr)^{js\,v}\qquad (x \in X),$$
--   the following three assertions hold for the integrand
--   $$F(x,z) = \xi_L(z)\Bigl( \sum_{\delta \in \mathcal{U}}^{f} \varphi\bigl(x^{-1}\,\delta\,{}^{\sigma_D}(z\cdot x)\bigr) - \mathbf{1}_{H_R}(z\cdot x)\,\mathrm{CT}_x(z\cdot x)\Bigr),$$
--   in which: $\delta \in \mathrm{GL}_2(L)$ is viewed in $\mathrm{GL}_2(\mathbb{A}_L)$ by `globalPoints`; $z \cdot x$ denotes `centralScalar` $z$ times $x$; ${}^{\sigma_D}(\cdot)$ is `sigmaAdelicAct K L D σ`, the entrywise action of the ring automorphism $D.\mathrm{act}\,\sigma$; the (finite-support) sum runs over the set $\mathcal{U}$ of those $\delta \in \mathrm{GL}_2(L)$ for which there is $\gamma$ in `unipotentCell K` (i.e. $\gamma \in \mathrm{GL}_2(K)$ whose matrix does not satisfy `IsCentralType` and has characteristic polynomial $(X-a)^2$ for some $a \in K$) with `normClassMap hgen` of the $\sigma$-twisted class of $\delta$ equal to the conjugacy class of $\gamma$; $H_R$ is the set of $g$ with $\exp R <$ `adelicHeight L` $g$; and
--   $$\mathrm{CT}_x(y) = \int_{\mathbb{A}_L} \ \sum_{\delta \in \mathcal{P}}^{f} \varphi\bigl(x^{-1}\,\delta\,{}^{\sigma_D}(n(t)\,y)\bigr)\,\mathrm{d}\nu(t),$$
--   where $n(t) =$ `unipotentGL2 t`, $\mathcal{P}$ is the set of $\gamma \in \mathrm{GL}_2(L)$ with $\gamma_{10}=0$ and $\mathrm{Norm}_{L/K}(\gamma_{00}/\gamma_{11}) = 1$, and the measurable structure and measure are the fields `nS` and `ν` of the record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, namely the Borel $\sigma$-algebra of $\mathbb{A}_L$ and the additive adelic Haar measure conditioned on the adelic box `adelicBox L`.
--
--   The three assertions are: (i) for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ the function $z \mapsto F(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$; (ii) the function $x \mapsto \int_{\Omega_L} F(x,z)\,\mathrm{d}\nu_{Z,L}(z)$ is integrable on $\Phi_0$ with respect to `adelicGLHaar`; and (iii)
--   $$\int_{\Phi_0}\int_{\Omega_L} F(x,z)\,\mathrm{d}\nu_{Z,L}(z)\,\mathrm{d}x = R\,\nu(g) + \mu(g),$$
--   with $R$ read in $\mathbb{C}$: the truncated unipotent contribution is an affine function of the truncation parameter $R$, with coefficients $\nu(g)$ and $\mu(g)$ independent of $R$.
--
--   This is the unipotent-type contribution to the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L/K$, evaluated against Hecke words at a set $T$ of places unramified in $L/K$ and truncated at adelic height $\exp R$: the statement packages its dependence on $R$ as an affine function whose two coefficients are continuous functionals on $C(X,\mathbb{C})$, the second of which carries no mass near any prescribed point of the $T$-coordinates. It is used in the comparison of geometric sides at matching places, in the passage to the limit $R \to \infty$ for unit factorizations, and in the bound for the twisted adelic kernel with its central-elliptic terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram.lean

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

theorem AutomorphicForm.forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
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
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
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
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
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
      (R : ℂ) * ν g + μ g := by sorry
