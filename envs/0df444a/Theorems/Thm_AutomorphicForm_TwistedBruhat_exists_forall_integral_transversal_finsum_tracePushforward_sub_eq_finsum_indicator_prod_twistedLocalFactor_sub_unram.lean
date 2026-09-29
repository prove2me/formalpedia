-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
-- name    : AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/036f0377-bbfc-5b07-a9bc-49b711c2de8f
-- title:
--   Twisted unipotent term: transversal descent to rank-one Tate data
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ Galois, $\nu_{Z_L}$ is a Haar measure on the idele group $\mathbb{A}_L^{\times}$ (taken with its Borel structure) and $\mu_K$ is an additive Haar measure on $\mathbb{A}_K$.
--
--   **Galois descent data.** $D$ is an `IdeleGaloisDescent` datum for $L/K$, i.e. a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ whose members are continuous and compatible with $L \to \mathbb{A}_L$; $\sigma \in \mathrm{Gal}(L/K)$ satisfies `hgen`, namely every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, so the group is cyclic with generator $\sigma$. The induced action on ideles is [`M4aHerbrand.IdeleGaloisDescent.unitsAct D σ`](def/M4aHerbrand_IdeleClassVocab.html#L41), and [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) is the entrywise action on $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   **Character data.** $\xi_L$ is a homomorphism from the full subgroup $\top \le \mathbb{A}_L^{\times}$ to $\mathbb{C}^{\times}$; `hξc` states that $z \mapsto \xi_L(z)$ is continuous as a $\mathbb{C}$-valued function, `hξt` that $\xi_L$ is trivial on the image of $L^{\times}$ in $\mathbb{A}_L^{\times}$, and `hξσ` that $\xi_L$ is invariant under the $\sigma$-action on ideles given by $D$.
--
--   **Place data.** $S_L$ is a finite set of finite places of $L$ containing, by `hSL`, every $w$ whose ramification index $e(w / w|_K)$ is not $1$. $S$ and $T$ are finite sets of finite places of $K$; `hT` requires that no place of $L$ above a place of $T$ lies in $S_L$. $\varphi_a$ is a function on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ and $\varphi_S$ assigns to each finite place $v$ of $K$ a function on $\mathrm{GL}_2(L \otimes_K K_v)$. $S_\tau$ is a finite set of finite places of $K$ characterised by `hSτ`: $v \in S_\tau$ if and only if either $v \in S$ and $v \notin T$, or some place $w$ of $L$ above $v$ has $e(w/v) \neq 1$.
--
--   **Word data.** For each finite place $v$ of $K$, $w_v =$ `ws v` is a place of $L$ above $v$, $n_v =$ `ns v` is a natural number, `rTs v` is a family of $n_v$ elements of $\mathrm{GL}_2(L_{w_v})$ and $z_v =$ `zs v` is an element of $\mathrm{GL}_2(L_{w_v})$.
--
--   **Transversal data.** $n$ is a natural number, $c : \mathrm{Fin}\,n \to \mathbb{R}$, and for each $j$ there are: a measure $\tau_j$ on $\mathbb{A}_L^{\times}$ (for the idele Borel structure), measures $\tau^{\mathrm{fin}}_{j,v}$ on $(L \otimes_K K_v)^{\times}$ for finite $v$, measures $\tau^{\mathrm{arch}}_{j,v}$ on $\bigl(\prod_{w \mid v} L_w\bigr)^{\times}$ for infinite places $v$ of $K$, and elements $\pi_{j,v} \in (L \otimes_K K_v)^{\times}$. The hypotheses on these are: `hcpos`, $c_j > 0$; `hlev`, $\tau_j$ gives measure zero to the set of $t$ with idele norm $\ne c_j$; `hτfin`, each $\tau_j$ is finite on compact sets; `hτ0`, $\tau_j$ vanishes on the complement of [`AutomorphicForm.TransversalMeasure.saturated K L Sτ`](def/AutomorphicForm_TransversalMeasure.html#L89), the set of ideles $t$ whose semi-local component at every $v \notin S_\tau$ lies in the product of the integral units with the range of `includeUnits`; `hgood`, for $v \notin S_\tau$ the measure $\tau^{\mathrm{fin}}_{j,v}$ is a Haar measure on $(L \otimes_K K_v)^{\times}$ normalised and restricted to the subgroup `integralUnits K L v` (the units of the image of $\mathcal{O}_L \otimes \mathcal{O}_{K_v}$); `hgood'`, for $v \notin S_\tau$ the measure of the complement of that subgroup is $0$ and its measure is $1$; `hbad`, for $v \in S_\tau$ the measure $\tau^{\mathrm{fin}}_{j,v}$ is the translate by $\pi_{j,v}$ of the push-forward to $(L \otimes_K K_v)^{\times}$ of a Haar measure on the norm-one subgroup `normOneUnits K L v`; `harch`, each $\tau^{\mathrm{arch}}_{j,v}$ is the push-forward of a Haar measure on `archNormOneUnits K L v`; and `hfac3`, the factorisation property: for every $j$, every finite set $S_f \supseteq S_\tau$ of finite places and all families $f_v$ on $(L \otimes_K K_v)^{\times}$ and $g_v$ on $\bigl(\prod_{w\mid v} L_w\bigr)^{\times}$ with values in $[0,\infty]$, measurable for $v \in S_f$ respectively for all infinite $v$, the lower integral against $\tau_j$ of the product of the $g_v$ at the archimedean semi-local components, of the $f_v$ for $v \in S_f$ at the semi-local components, and of the indicator of the set of $t$ whose semi-local component at each $v \notin S_f$ is an integral unit, equals $\bigl(\prod_{v \mid \infty} \int^- g_v \, d\tau^{\mathrm{arch}}_{j,v}\bigr) \cdot \prod_{v \in S_f} \int^- f_v \, d\tau^{\mathrm{fin}}_{j,v}$.
--
--   **Conclusion.** There exist a finite set $S_x$ of finite places of $K$, archimedean factors $g_j : \mathbb{A}_{K,\infty} \to \mathbb{C}$ and local factors $h_{0,j,v} : K_v \to \mathbb{C}$ (one for each $j$ and each finite place $v$), none of them depending on the word exponents, such that the following three assertions hold.
--
--   First, $S \cup T \subseteq S_x$.
--
--   Second, for all $k_\bullet, j_\bullet : \{\text{finite places of } K\} \to \mathbb{N}$ and every $j$, the function
--   $$\Psi_{j,k_\bullet,j_\bullet}(x) = \mathbf{1}_{\mathrm{integralOutside}\,S_x}(x)\; g_j(x_\infty) \prod_{v \in S_x} F_{j,v}\bigl(x_{\mathrm{fin},v}\bigr),$$
--   where $\mathrm{integralOutside}\,S_x$ is the set of adeles whose finite component is integral at every $v \notin S_x$, and where $F_{j,v} =$ [`twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v)`](def/TwistedUnipotentTerm_SemiLocalOrbitalVocab.html#L85) for $v \in T$ — the local trace push-forward to $K_v$ of the local unipotent orbital function `unipotentOrbitalFn` attached to $\xi_L$, the place $w_v$, the matrices `rTs v`, $z_v$ and the exponents $k_v, j_v$ — and $F_{j,v} = h_{0,j,v}$ otherwise, belongs to the Schwartz–Bruhat space [`NumberField.AdelicFourier.schwartzBruhat K`](def/NumberField_AdelicFourier.html#L80) (the $\mathbb{C}$-span of products of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles) and has compact support.
--
--   Third, for all $k_\bullet, j_\bullet$ as above, for every $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{L,\mathrm{fin}})$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds with semi-local factors given at $v \in T$ by
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\mathrm{semiLocalIntegralSet}}\Bigl(\bigl(\text{semi-local component at } v \text{ of } \mathrm{localEmbed}_{w_v}\bigl(\textstyle\prod_m (\mathrm{rTs}\,v)(\iota(m)) \cdot z_v^{\,j_v}\bigr)\bigr)^{-1} x\Bigr)$$
--   (the indicator taking the value $1$) and at the remaining places by $\varphi_S(v)$ — that is, $\varphi_a$ is an archimedean test factor, $\varphi_f$ a locally constant compactly supported finite test factor, the listed semi-local functions are locally constant with compact support at the places of $S \cup T$, $\varphi_f$ is the product of the semi-local factors at the semi-local components on matrices that are integral outside $S \cup T$ and vanishes otherwise, and $\varphi$ is the product of $\varphi_a$ at the archimedean part with $\varphi_f$ at the finite part — the following two statements hold for every $j$, every $y \in \mathbb{A}_K^{\times}$ and every $\theta \in \mathbb{R}$.
--
--   Put, for $t \in \mathbb{A}_L^{\times}$, $k$ in the adelic maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ and $\zeta \in \mathbb{A}_L^{\times}$,
--   $$G_{t,k,\zeta}(w) = \varphi\Bigl(k^{-1}\, n(w t^{-1})\, \mathrm{diag}\bigl(\sigma_D(t)\,t^{-1},\,1\bigr)\, z\bigl(\sigma_D(\zeta)\bigr)\, \sigma_D(k)\Bigr), \qquad w \in \mathbb{A}_L,$$
--   where $n(\cdot)$ is the upper unipotent matrix `unipotentGL2`, $\mathrm{diag}(\cdot,1)$ is `diagOne`, $z(\cdot)$ is the central scalar matrix, and $\sigma_D$ denotes the action of $\sigma$ through $D$ on ideles and on $\mathrm{GL}_2(\mathbb{A}_L)$; and let $G^{\flat}_{t,k,\zeta} =$ `tracePushforward K L G_{t,k,ζ}` be its push-forward to $\mathbb{A}_K$, i.e. $r \mapsto \int G_{t,k,\zeta}(\mathrm{traceFibre}\,r\,w)\,dw$ against the product adelic additive Haar measure.
--
--   (a) The iterated lower integral
--   $$\int^-_t \int^-_k \int^-_\zeta \Bigl\| \xi_L(\zeta)\Bigl( \sum_{\eta \in K^{\times}}^{\mathrm{f}} G^{\flat}_{t,k,\zeta}\bigl(\eta\, y^{-1}\bigr) - \bigl[\theta < \|y\|_K\bigr]\,\|y\|_K \int_{\mathbb{A}_K} G^{\flat}_{t,k,\zeta}(u)\, d\mu_K(u)\Bigr)\Bigr\|_{e} \, d\nu_{Z_L}\, d\,\mathrm{maximalCompactHaar}\,L \, d\tau_j$$
--   is finite, where $\sum^{\mathrm{f}}$ is the finite sum over $\eta \in K^{\times}$, $\eta$ is viewed in $\mathbb{A}_K$, $\|y\|_K$ is the idele norm [`NumberField.TateGlobal.ideleNorm K y`](def/NumberField_TateGlobalZeta.html#L19), and the bracket denotes the value $0$ when $\theta \ge \|y\|_K$.
--
--   (b) The corresponding Bochner iterated integral
--   $$\int_t \int_k \Bigl(\int_\zeta \xi_L(\zeta)\Bigl( \sum_{\eta \in K^{\times}}^{\mathrm{f}} G^{\flat}_{t,k,\zeta}\bigl(\eta\, y^{-1}\bigr) - \bigl[\theta < \|y\|_K\bigr]\,\|y\|_K \int G^{\flat}_{t,k,\zeta}\, d\mu_K\Bigr) d\nu_{Z_L}\Bigr) d\,\mathrm{maximalCompactHaar}\,L \; d\tau_j$$
--   equals
--   $$\sum_{\eta \in K^{\times}}^{\mathrm{f}} \Psi_{j,k_\bullet,j_\bullet}\bigl(\eta\, y^{-1}\bigr) - \bigl[\theta < \|y\|_K\bigr]\,\|y\|_K \int_{\mathbb{A}_K} \Psi_{j,k_\bullet,j_\bullet}(u)\, d\mu_K(u),$$
--   with $\Psi_{j,k_\bullet,j_\bullet}$ the Schwartz–Bruhat function of the second assertion.
--
--   This is the final descent step for the unipotent-type term of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension: after the torus variable has been integrated over a transversal, each piece of the twisted unipotent term is identified with the rank-one Tate datum on $\mathbb{A}_K$ given by a Schwartz–Bruhat function that is a pure tensor, carrying the twisted local orbital factors at the Hecke places of $T$, with the lattice sum over $K^{\times}$ and the constant-term truncation taken outside the transversal integrals. It is used in the comparison of the Iwasawa-decomposed cusp kernel with its truncation, expressing the difference as a sum of rank-one set integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram.lean

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
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
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
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1)
    (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L))
    (τfin : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), Measure (L ⊗[K] v.adicCompletion K)ˣ)
    (τarch : Fin n → ∀ v : InfinitePlace K, Measure (∀ w : v.Extension L, w.1.Completion)ˣ)
    (πs : Fin n → ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hgood : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      ∃ μ : Measure (L ⊗[K] v.adicCompletion K)ˣ, μ.IsHaarMeasure ∧
        τfin j v = (μ (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))⁻¹ •
          μ.restrict (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ))
    (hgood' : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∉ Sτ →
      τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ)ᶜ = 0 ∧
        τfin j v (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) = 1)
    (hbad : ∀ j (v : HeightOneSpectrum (𝓞 K)), v ∈ Sτ →
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.normOneUnits K L v), μN.IsHaarMeasure ∧
        τfin j v = Measure.map (fun x => πs j v * x) (Measure.map Subtype.val μN))
    (harch : ∀ j (v : InfinitePlace K),
      ∃ μN : Measure (AutomorphicForm.TransversalMeasure.archNormOneUnits K L v), μN.IsHaarMeasure ∧
        τarch j v = Measure.map Subtype.val μN)
    (hfac3 : ∀ j (Sf : Finset (HeightOneSpectrum (𝓞 K))), Sτ ⊆ Sf →
      ∀ (f : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ → ℝ≥0∞)
        (g : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ → ℝ≥0∞),
        (∀ v ∈ Sf, Measurable (f v)) → (∀ v, Measurable (g v)) →
        ∫⁻ t, (∏ v : InfinitePlace K, g v (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t)) *
            (∏ v ∈ Sf, f v (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)) *
            Set.indicator {t | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
                AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
                  AutomorphicForm.TransversalMeasure.integralUnits K L v}
              (fun _ => (1 : ℝ≥0∞)) t ∂(τ j) =
          (∏ v : InfinitePlace K, ∫⁻ x, g v x ∂(τarch j v)) * ∏ v ∈ Sf, ∫⁻ x, f v x ∂(τfin j v)) :
    ∃ (Sx : Finset (HeightOneSpectrum (𝓞 K))) (g : Fin n → InfiniteAdeleRing K → ℂ)
      (h₀ : Fin n → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ),
      S ∪ T ⊆ Sx ∧
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
        ∀ (j : Fin n) (y : (AdeleRing (𝓞 K) K)ˣ) (θ : ℝ),
          (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0))‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂(τ j)) ≠ ⊤ ∧
            (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if θ < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) =
            ((∑ᶠ η : Kˣ, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x)
                (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
              (if θ < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (fun x : AdeleRing (𝓞 K) K => (NumberField.TateGlobal.integralOutside Sx).indicator
            (fun x => g j x.1 * ∏ v ∈ Sx,
              (if v ∈ T then twistedLocalFactor K L D σ ξL v (ws v) (ns v) (rTs v) (zs v) (ks v) (js v) else h₀ j v)
                ((x.2 : FiniteAdeleRing (𝓞 K) K) v)) x) u ∂μK else 0)) := by sorry
