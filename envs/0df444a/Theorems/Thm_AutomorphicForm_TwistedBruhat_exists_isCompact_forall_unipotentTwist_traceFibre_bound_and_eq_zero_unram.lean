-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
-- name    : AutomorphicForm.TwistedBruhat.exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/cd70ec5d-13be-52a7-8bd9-bf073b8ce5f8
-- title:
--   Effective support, uniform bound and continuity of the twisted unipotent integrand
-- statement:
--   Setting. Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\nu_{Z,L}$ be a Haar measure on the idele unit group $(\mathbb{A}_L)^\times$ and let $\mu_K$ be an additive Haar measure on $\mathbb{A}_K$ (the measurable structures on these groups being the Borel ones). Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ that is continuous in each argument and compatible with $\mathrm{Gal}(L/K)$ acting on $L \hookrightarrow \mathbb{A}_L$; write $\sigma \cdot x$ for the action of the induced automorphism [`M4aHerbrand.IdeleGaloisDescent.unitsAct D σ`](def/M4aHerbrand_IdeleClassVocab.html#L41) of $(\mathbb{A}_L)^\times$. Let $\sigma \in \mathrm{Gal}(L/K)$, and let `hgen` assert that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$.
--
--   Ramification, character and test-function data. A finite set $S_L$ of primes of $L$ satisfies `hSL`: every $w$ whose ramification index over the prime of $K$ below it is $\neq 1$ belongs to $S_L$. A homomorphism $\xi_L$ from the full subgroup $\top \le (\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ is subject to three conditions: `hξc`, that $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous; `hξt`, that $\xi_L$ is trivial on the image of $L^\times$ in $(\mathbb{A}_L)^\times$; and `hξσ`, that $\xi_L(\sigma \cdot z_0) = \xi_L(z_0)$ for all $z_0$. Further data are a finite set $S$ of primes of $K$, a function $\varphi_a$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$, and functions $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for each prime $v$ of $K$; these enter only through the factorisation hypothesis in the conclusion. A second finite set $T$ of primes of $K$ satisfies `hT`: for $v \in T$, no prime $w$ of $L$ above $v$ lies in $S_L$. The Hecke-word data consist of a choice $w(v)$ of prime of $L$ above each $v$ (an element of `v.Extension (𝓞 L)`), integers $n_v =$ `ns v`, and elements `rTs v i` $(i < n_v)$ and `zs v` of $\mathrm{GL}_2(L_{w(v)})$. Finally, a finite set $S_\tau$ of primes of $K$ is pinned by `hSτ`: $v \in S_\tau$ if and only if either $v \in S$ and $v \notin T$, or some prime $w$ of $L$ above $v$ has ramification index $\neq 1$ over $v$.
--
--   Transversal measure data. Let $n \in \mathbb{N}$, let $c : \mathrm{Fin}\,n \to \mathbb{R}$, let $\tau_j$ be Borel measures on $(\mathbb{A}_L)^\times$, let $\tau_{\mathrm{fin},j,v}$ be measures on $(L \otimes_K K_v)^\times$ and $\tau_{\mathrm{arch},j,v}$ measures on $\bigl(\prod_{w \mid v} L_w\bigr)^\times$ for $v$ an infinite place of $K$, and let $\pi_{j,v} \in (L \otimes_K K_v)^\times$. These satisfy: `hcpos`, $c_j > 0$; `hlev`, $\tau_j$ gives measure zero to the set of $t$ with [`NumberField.TateGlobal.ideleNorm L t`](def/NumberField_TateGlobalZeta.html#L19) $\neq c_j$, the idele norm being the `distribHaarChar` of multiplication by $t$ on $\mathbb{A}_L$; `hτfin`, each $\tau_j$ is finite on compact sets; `hτ0`, $\tau_j$ gives measure zero to the complement of [`AutomorphicForm.TransversalMeasure.saturated K L Sτ`](def/AutomorphicForm_TransversalMeasure.html#L89), the set of $t$ whose semi-local component at each $v \notin S_\tau$ lies in the product of the integral units with the range of `includeUnits`; `hgood`, for $v \notin S_\tau$ the measure $\tau_{\mathrm{fin},j,v}$ is the restriction of some Haar measure $\mu$ to the integral units `integralUnits K L v` (the units of the image of `tensorAdicCompletionIntegersTo`), normalised by $\mu(\text{integral units})^{-1}$; `hgood'`, for $v \notin S_\tau$ the same measure annihilates the complement of the integral units and gives them mass $1$; `hbad`, for $v \in S_\tau$ the measure $\tau_{\mathrm{fin},j,v}$ is the translate by $\pi_{j,v}$ of the pushforward along inclusion of a Haar measure on `normOneUnits K L v` (the kernel of the valuation composed with the $K_v$-algebra norm); `harch`, each $\tau_{\mathrm{arch},j,v}$ is the pushforward along inclusion of a Haar measure on `archNormOneUnits K L v` (the kernel of the absolute value of the $K_v$-algebra norm); and `hfac3`, the product formula asserting that for every $j$ and every finite set $S_f \supseteq S_\tau$ and all families $f_v$ on $(L \otimes_K K_v)^\times$ and $g_v$ on $\bigl(\prod_{w\mid v} L_w\bigr)^\times$ with values in $[0,\infty]$, measurable for $v \in S_f$ respectively for all infinite $v$, the lower integral against $\tau_j$ of $\bigl(\prod_{v \mid \infty} g_v(\text{arch. semi-local component of } t)\bigr)\bigl(\prod_{v \in S_f} f_v(\text{semi-local component of } t)\bigr)$ times the indicator of the set of $t$ whose semi-local components outside $S_f$ are integral units equals $\bigl(\prod_{v \mid \infty} \int g_v \, d\tau_{\mathrm{arch},j,v}\bigr)\prod_{v \in S_f} \int f_v \, d\tau_{\mathrm{fin},j,v}$.
--
--   Conclusion. Let $k_v =$ `ks v` and $j_v =$ `js v` be natural numbers attached to the primes of $K$, let $\varphi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ one on $\mathrm{GL}_2$ of the finite adeles of $L$, and assume `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds with semi-local factors given at $v \in T$ by
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}\,k_v \to \mathrm{Fin}\,n_v} \mathbf{1}_{\,\mathrm{semiLocalIntegralSet}\ K\ L\ v}\Bigl(\bigl(\mathrm{semiLocalComponent}\ K\ L\ v\,\mathrm{AdelicDock.localEmbed}\bigl(\textstyle\prod_{m} \mathrm{rTs}\ v\ (\iota\ m) \cdot (\mathrm{zs}\ v)^{\,j_v}\bigr)\bigr)^{-1} x\Bigr),$$
--   the product over $m$ being taken in the order of `List.ofFn`, the embedding being the splice of a matrix over $L_{w(v)}$ into the identity at all other finite places, and the integral set consisting of those $g$ with both $g$ and $g^{-1}$ having entries in the image of `tensorAdicCompletionIntegersTo`; at $v \notin T$ the factor is $\varphi_{S,v}$. Thus $\varphi_a$ is a smooth compactly supported function of the archimedean matrix entries, $\varphi_f$ is locally constant with compact support, each factor at $v \in S \cup T$ is locally constant with compact support, $\varphi_f$ is the product of these factors at a matrix all of whose components outside $S \cup T$ are integral and vanishes otherwise, and $\varphi$ is the product of $\varphi_a$ on the archimedean part with $\varphi_f$ on the finite part.
--
--   Then for every $j \in \mathrm{Fin}\,n$ there exist compact sets $C_t, C_z \subseteq (\mathbb{A}_L)^\times$, $C_r \subseteq \mathbb{A}_K$ and $C_w \subseteq \mathbb{A}_K^{\,d}$, where $d = \dim_K \ker(\mathrm{Tr}_{L/K})$, and a real $M \ge 0$, such that, writing
--   $$\Phi(t,k,\zeta,r,w') = \varphi\bigl(k^{-1}\, n\bigl(\mathrm{traceFibre}\ K\ L\ r\ w' \cdot t^{-1}\bigr)\, \mathrm{diag}(\sigma \cdot t \cdot t^{-1},\,1)\, \bigl((\sigma \cdot \zeta) I\bigr)\, \sigma(k)\bigr)$$
--   for $t \in (\mathbb{A}_L)^\times$, $k$ in the subgroup `adelicMaximalCompact L` of those elements of $\mathrm{GL}_2(\mathbb{A}_L)$ whose finite part is integral of level $\top$ and whose component at each infinite place is a row isometry, $\zeta \in (\mathbb{A}_L)^\times$, $r \in \mathbb{A}_K$ and $w' \in \mathbb{A}_K^{\,d}$ — here $n(\cdot)$ is the upper unipotent matrix `unipotentGL2`, $\mathrm{diag}(a,1)$ is `diagOne`, $(\cdot) I$ is `centralScalar`, $\sigma(k)$ denotes [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) applied entrywise to $k$, and `traceFibre K L r w'` is $\mathrm{genuine}\beta(r)\cdot [L:K]^{-1} + \sum_i \mathrm{genuine}\beta(w'_i)\cdot b_i$ with $b_i$ the chosen $K$-basis of $\ker(\mathrm{Tr}_{L/K})$ — the following five assertions hold: $\|\Phi(t,k,\zeta,r,w')\| \le M$ for all arguments; $\Phi(t,k,\zeta,r,w') = 0$ whenever $\zeta \notin C_z$; for $\tau_j$-almost every $t$, if $t \notin C_t$ then $\Phi(t,k,\zeta,r,w') = 0$ for all $k,\zeta,r,w'$; for every $t \in C_t$ and all $k,\zeta,r,w'$ with $r \notin C_r$ or $w' \notin C_w$ one has $\Phi(t,k,\zeta,r,w') = 0$; and $\Phi$, regarded as a function on $\bigl((\mathbb{A}_L)^\times \times \mathrm{adelicMaximalCompact}\ L\bigr) \times \bigl((\mathbb{A}_L)^\times \times (\mathbb{A}_K \times \mathbb{A}_K^{\,d})\bigr)$, is continuous.
--
--   This is the analytic frame for the interchange and Fubini steps in the descent of the unipotent-type term of a twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$ to rank one: it produces an effective compact domain in the transversal, central, and trace-adapted unipotent variables, a uniform bound, and continuity of the unfolded integrand, in the unramified-transversal situation. It is used by the computations of integral transversals that identify the unfolded integral with an indicator times a product of twisted local factors, and by the comparison of the trace-pushforward sums with the transversal sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram.lean

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

theorem AutomorphicForm.TwistedBruhat.exists_isCompact_forall_unipotentTwist_traceFibre_bound_and_eq_zero_unram
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
        ∀ j : Fin n,
          ∃ (Ct : Set (AdeleRing (𝓞 L) L)ˣ) (Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cr : Set (AdeleRing (𝓞 K) K))
            (Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) (M : ℝ),
            IsCompact Ct ∧ IsCompact Cz ∧ IsCompact Cr ∧ IsCompact Cw ∧ 0 ≤ M ∧
            (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              ‖φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))‖ ≤ M) ∧
            (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              ζ ∉ Cz → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            (∀ᵐ t ∂(τ j), t ∉ Ct → ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            (∀ t ∈ Ct, ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
              (r ∉ Cr ∨ w' ∉ Cw) → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
            Continuous (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
                ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
                  (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
              (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
                  (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
                φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by sorry
