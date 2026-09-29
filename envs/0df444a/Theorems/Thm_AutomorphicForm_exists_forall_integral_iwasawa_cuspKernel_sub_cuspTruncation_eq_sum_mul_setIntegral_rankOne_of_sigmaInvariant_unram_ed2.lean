-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
-- name    : AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/a6f86b2e-71ee-5632-ba31-901331051d3e
-- title:
--   Unipotent term in Iwasawa coordinates via rank-one Tate integrals
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ Galois, $\sigma \in \mathrm{Gal}(L/K)$, and $\|\cdot\|_L$, $\|\cdot\|_K$ denote the idele norms [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) (the module of the scaling action on the adeles). $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, and `AdelicGL2 (𝓞 L) L` is $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   The global data and standing hypotheses are: real numbers $\alpha, \beta$ with `hα` : $0 < \alpha$ and `hαβ` : $\alpha < \beta$; a Haar measure $\nu_{Z,L}$ on $\mathbb{A}_L^\times$ and a set $\Omega_L$ with `hΩL` asserting that $\Omega_L$ is a fundamental domain for the action of the image of $L^\times \to \mathbb{A}_L^\times$ on $\mathbb{A}_L^\times$ with respect to $\nu_{Z,L}$; a descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ which is continuous in each $\tau$ and compatible with $L \to \mathbb{A}_L$; the hypothesis `hgen` that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$; a finite set $S_L$ of primes of $\mathcal{O}_L$ and a character $\xi_L$ of the top subgroup of $\mathbb{A}_L^\times$ with values in $\mathbb{C}^\times$, subject to `hSL` (every prime $w$ of $\mathcal{O}_L$ whose ramification index over the prime of $\mathcal{O}_K$ below it is $\neq 1$ belongs to $S_L$), `hξc` (continuity of $z \mapsto \xi_L(z)$ as a complex-valued function), `hξt` ($\xi_L$ is trivial on principal ideles) and `hξσ` ($\xi_L(\mathrm{unitsAct}\,D\,\sigma\, z_0) = \xi_L(z_0)$ for all $z_0$, i.e. $\xi_L$ is invariant under the $\sigma$-action on ideles supplied by $D$); a finite set $S$ of primes of $\mathcal{O}_K$; fixed test data $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$ and $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for each prime $v$ of $\mathcal{O}_K$; an additive Haar measure $\mu_K$ on $\mathbb{A}_K$ with `hμK1` : $\mu_K(\mathrm{adelicBox}\,K) = 1$; a Haar measure $\nu_K$ on $\mathbb{A}_K^\times$ and a set $\Omega_K$ with `hΩK` asserting that $\Omega_K$ is a fundamental domain for the principal ideles of $K$ in $\mathbb{A}_K^\times$ with respect to $\nu_K$; additive Haar measures $\mu_f\,v$ on each completion $K_v$; a set $X \subseteq \mathbb{A}_L$ with `hX` asserting that $X$ is an additive fundamental domain for the principal subgroup $L \subset \mathbb{A}_L$ with respect to `adelicAddHaar (𝓞 L) L`; and sets $\Omega_1, \Omega_2 \subseteq \mathbb{A}_L^\times$ with `hΩ₁`, `hΩ₂` asserting that each is a fundamental domain for the principal ideles of $L$ with respect to [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391).
--
--   The conclusion is universally quantified over the following Hecke data at a set of good places. Let $T$ be a finite set of primes of $\mathcal{O}_K$ such that no prime of $S_L$ lies above any $v \in T$. Let $w_v$ be, for every prime $v$ of $\mathcal{O}_K$, a chosen prime of $\mathcal{O}_L$ above $v$ (an element of `v.Extension (𝓞 L)`), and let $w'$ be a map from primes of $\mathcal{O}_K$ to primes of $\mathcal{O}_L$ with $(w'\,v)$'s ideal equal to $\sigma \cdot (w_v)$'s ideal for $v \in T$; the datum $w'$ enters only through this condition. Let $\varpi_v$ be, for each $v$, an element of the valuation ring of $L_{w_v}$, irreducible for $v \in T$, with nonzero image $\varpi_v \in L_{w_v}$ for $v \in T$ (the hypothesis `hϖs0`, which is itself an argument of the statement). Let $n_v \in \mathbb{N}$ and $r_{v,i} \in \mathrm{GL}_2(L_{w_v})$ for $i \in \mathrm{Fin}(n_v)$ be such that for every $v \in T$ the family $(r_{v,i})_i$ is a Hecke coset system for the subgroup $U_v = \mathrm{image}\big(\mathrm{GL}_2(\mathcal{O}_{w_v}) \to \mathrm{GL}_2(L_{w_v})\big)$ and the element $\mathrm{diag}(\varpi_v, 1)$: each $r_{v,i}$ lies in the double coset $U_v\,\mathrm{diag}(\varpi_v,1)\,U_v$, every element of that double coset is congruent modulo $U_v$ to some $r_{v,i}$, and $i \mapsto r_{v,i}U_v$ is injective. Finally let $z_v \in \mathrm{GL}_2(L_{w_v})$ be such that for $v \in T$ the matrix of $z_v$ is the scalar matrix $\varpi_v \cdot 1$.
--
--   For such data there exist $n \in \mathbb{N}$, complex weights $\kappa_j$ ($j \in \mathrm{Fin}(n)$), reals $a_j$, a real $b$, a finite set $S_x$ of primes of $\mathcal{O}_K$, archimedean factors $g_j$ on the infinite adeles of $K$ and auxiliary local factors $h_{0,j,v} : K_v \to \mathbb{C}$, such that the following four assertions hold.
--
--   First, $a_j > 0$ for all $j$. Second, $b \neq 0$. Third, $S \cup T \subseteq S_x$.
--
--   Fourth, for all $k, j' : \{\text{primes of } \mathcal{O}_K\} \to \mathbb{N}$ and every index $j$, the function
--   $$\Psi_{j,k,j'}(x) = \mathbf{1}_{\mathrm{integralOutside}\,S_x}(x)\cdot\Big( g_j(x_\infty)\prod_{v \in S_x} F_{j,v}(x_v)\Big),$$
--   where $\mathrm{integralOutside}\,S_x = \{x \in \mathbb{A}_K : x_v \in \mathcal{O}_v \text{ for all } v \notin S_x\}$, and where $F_{j,v} =$ [`twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v)`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) for $v \in T$ and $F_{j,v} = h_{0,j,v}$ otherwise, lies in the Schwartz–Bruhat space [`NumberField.AdelicFourier.schwartzBruhat K`](def/NumberField_AdelicFourier.html#L80) (the $\mathbb{C}$-span of products of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles) and has compact support. Here [`twistedLocalFactor`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) is, by definition, the pushforward along the local trace, `AdelicTracePushforward.localTracePushforward K L v`, of the function [`TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v)`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L57) on $L \otimes_K K_v$: its value at $r \in K_v$ is the integral of that function over the fibre of the trace above $r$, against a product of copies of the additive Haar measure on $K_v$ normalised by the inverse of the measure of $\mathcal{O}_v$.
--
--   Fifth, for all $k, j'$ as above, every $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ satisfying `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` with semi-local data given by
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\mathrm{semiLocalIntegralSet}\,K\,L\,v}\Big( \big(\mathrm{semiLocalComponent}_v(\mathrm{localEmbed}_{w_v}( r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}\cdot z_v^{\,j'_v})) \big)^{-1} x\Big)$$
--   at the places $v \in T$ and by $\varphi_{S,v}$ at the remaining places of $S \cup T$ — that is: $\varphi_a$ is an archimedean test factor (smooth in the matrix entries and compactly supported), $\varphi_f$ is locally constant with compact support, each of the above local functions at $v \in S \cup T$ is locally constant with compact support, $\varphi_f(h)$ equals the product over $v \in S \cup T$ of the local functions evaluated at the semi-local components of $h$ whenever all components off $S \cup T$ are integral, $\varphi_f(h) = 0$ as soon as some component off $S \cup T$ fails to be integral, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_f)$ — and every real $R$, the following holds.
--
--   Assume two finiteness hypotheses. The first is that the iterated lower integral
--   $$\int^-_{x \in X}\int^-_{u \in \Omega_1}\int^-_{t \in \Omega_2}\int^-_{k} \big\| \mathbf{1}_{\{g\,:\,\|\det g\|_L \in [\alpha,\beta]\}}\!\cdot\! G\big(\mathbf{u}(x)\,z(u)\,\mathrm{diag}(t,1)\,k\big)\cdot \|t\|_L^{-1}\big\|_e$$
--   is $\neq \infty$, where $\mathbf{u}(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, $z(u)$ is the central scalar matrix with entry $u$, $k$ runs over the adelic maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to `maximalCompactHaar L`, the measures on $u, t$ are [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391) and the measure on $x$ is `adelicAddHaar (𝓞 L) L`, and
--   $$G(g) = \int_{z \in \Omega_L} \xi_L(z)\big( \mathrm{cuspKernel}(\varphi, z, g) - \mathrm{cuspTruncation}(R, \varphi, z, g)\big)\,d\nu_{Z,L}.$$
--   Here `TwistedBruhat.cuspKernel K L D σ hgen φ z g` is the finite sum over $\beta \in \mathrm{normUnipotentSet} \cap B(L)$ of $\varphi\big(g^{-1}\,\iota(\beta)\, \sigma_*(z\cdot g)\big)$, where $\iota$ is the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$, $\sigma_*$ is the entrywise action of $D(\sigma)$, $B(L)$ is the subgroup of matrices with vanishing $(1,0)$ entry, and $\mathrm{normUnipotentSet}$ is the set of $\delta \in \mathrm{GL}_2(L)$ whose $\sigma$-twisted norm class is the conjugacy class of some unipotent-type element of $\mathrm{GL}_2(K)$; and `TwistedBruhat.cuspTruncation K L D σ R φ z g` is the indicator, on the set where the adelic height exceeds $e^R$, of the constant term along the unipotent subgroup — the integral over $t$ against the conditional measure of `adelicAddHaar (𝓞 L) L` on `adelicBox L` of $y \mapsto \sum_{\delta \in \mathrm{borelNormOneSet}} \varphi(g^{-1}\iota(\delta)\sigma_*(y))$ composed with $t \mapsto \mathbf{u}(t)\cdot{}$ — evaluated at $z \cdot g$, where $\mathrm{borelNormOneSet}$ consists of the $\gamma$ with $\gamma_{10} = 0$ and $N_{L/K}(\gamma_{00}/\gamma_{11}) = 1$.
--
--   The second finiteness hypothesis is that the same fourfold lower integral, with $G$ replaced by the function
--   $$g \mapsto \int^-_{z \in \Omega_L} \|\xi_L(z)\|_e \sum_{s \in L^\times}\ \sum_{a \in \{a \in L^\times : N_{L/K}(a) = 1\}} \big\| A_{s,a}(z,g) - B_{s,a}(z,g)\big\|_e\,d\nu_{Z,L},$$
--   and with $\|t\|_L^{-1}$ replaced by $\mathrm{ofReal}\,\|t\|_L^{-1}$, is $\neq \infty$; here $A_{s,a}(z,g)$ is the finite sum of $\varphi(g^{-1}\iota(\delta)\sigma_*(z\cdot g))$ over those $\delta \in \mathrm{normUnipotentSet}$ with $\delta_{10} = 0$, $\delta_{11} = s$, $\delta_{00} = s\,a$, and $B_{s,a}(z,g)$ is the indicator, on the set where the adelic height of $L$ exceeds $e^R$, of the constant term along $t \mapsto \mathbf{u}(t)$ with respect to the conditional measure of `adelicAddHaar (𝓞 L) L` on `adelicBox L` of $y \mapsto \sum_{\delta} \varphi(g^{-1}\iota(\delta)\sigma_*(y))$, the sum being over the $\delta$ with $\delta_{10} = 0$, $\delta_{11} = s$, $\delta_{00} = s\,a$, evaluated at $z \cdot g$.
--
--   Under these two hypotheses the asserted identity is
--   $$\int_{x \in X}\int_{u \in \Omega_1}\int_{t \in \Omega_2}\int_{k} \mathbf{1}_{\{g\,:\,\|\det g\|_L \in [\alpha,\beta]\}}\!\cdot\! G\big(\mathbf{u}(x)\,z(u)\,\mathrm{diag}(t,1)\,k\big)\cdot \|t\|_L^{-1}$$
--   $$= \sum_{j} \kappa_j \int_{y \in \Omega_K} \|y\|_K^{-1}\Big( \sum_{\eta \in K^\times} \Psi_{j,k,j'}\big(\eta\, y^{-1}\big) - \Big[\,\|y\|_K > a_j e^{bR} \ ?\ \|y\|_K \int_{\mathbb{A}_K} \Psi_{j,k,j'}\,d\mu_K \ :\ 0\,\Big]\Big)\,d\nu_K,$$
--   with the integrals on the left taken in the order and against the measures listed above, the sum over $\eta$ a finite sum over the type $K^\times$, $\eta\,y^{-1}$ meaning the product of the image of $\eta$ in $\mathbb{A}_K$ with the adele underlying $y^{-1}$, and $\Psi_{j,k,j'}$ the function of the fourth assertion. Thus the weights $\kappa_j$, thresholds $a_j$, rate $b$, set $S_x$ and factors $g_j, h_{0,j,v}$ do not depend on the Hecke word $(k,j')$, on $\varphi$, $\varphi_f$ or on $R$.
--
--   This is the descent step for the unipotent-type contribution to the $\sigma$-twisted trace formula for $\mathrm{GL}(2)$ over a cyclic extension $L/K$: after Iwasawa unfolding, the truncated unipotent-type part of the twisted kernel is identified with a finite combination, independent of the Hecke word, of truncated rank-one Tate integrals over $K$. It is used by [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_sum_mul_setIntegral_rankOne_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2.lean

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
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem
    AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
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
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] (hμK1 : μK (NumberField.AdelicBox.adelicBox K) = 1)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νK : Measure (AdeleRing (𝓞 K) K)ˣ) [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μf : (v : HeightOneSpectrum (𝓞 K)) → Measure (v.adicCompletion K)) [∀ v, (μf v).IsAddHaarMeasure]
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hX : @IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 L) L) _ _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 L) L) X (adelicAddHaar (𝓞 L) L))
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hΩ₂ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂ (NumberField.Idele.idelicHaar L))
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩) :
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
      ∀ R : ℝ,
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            ‖Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)‖ₑ
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ →
      ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * g))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ (g⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * g)‖ₑ ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤ →
      (∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
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
