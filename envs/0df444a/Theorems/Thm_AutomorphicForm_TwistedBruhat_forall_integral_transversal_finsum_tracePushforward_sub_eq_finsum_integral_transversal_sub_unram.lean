-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
-- name    : AutomorphicForm.TwistedBruhat.forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3780e1c0-a5c5-55b4-8bfb-9d06e2246cc7
-- title:
--   Lattice sum and constant term commute with transversal integrals
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ Galois, and all measurable structures on adelic groups, on semi-local unit groups $(L \otimes_K K_v)^\times$, on archimedean semi-local unit groups and on $\mathrm{GL}_2$ of an adele ring are the Borel ones.
--
--   **Descent and measure data.** $D$ is an element of [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism `D.act` from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the Galois action on $L$ through `algebraMap L (AdeleRing (𝓞 L) L)` and whose automorphisms are continuous; [`M4aHerbrand.IdeleGaloisDescent.unitsAct D σ`](def/M4aHerbrand_IdeleClassVocab.html#L41) denotes the induced automorphism of $\mathbb{A}_L^\times$ and [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$. The element $\sigma \in \mathrm{Gal}(L/K)$ satisfies `hgen`: every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$. Further, $\nu_{Z_L}$ is a Haar measure on $\mathbb{A}_L^\times$, $\mu_K$ an additive Haar measure on $\mathbb{A}_K$, and `maximalCompactHaar L` the Haar measure on `adelicMaximalCompact L`, the subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose finite part lies in `finiteIntegralGL2` and each of whose archimedean components is a row isometry.
--
--   **Character data.** $\xi_L$ is a homomorphism from the full subgroup $\top \le \mathbb{A}_L^\times$ to $\mathbb{C}^\times$, subject to: `hξc`, the map $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous; `hξt`, $\xi_L$ is trivial on the principal ideles, the range of `Units.map (algebraMap L (AdeleRing (𝓞 L) L))`; and `hξσ`, $\xi_L$ is invariant under `unitsAct D σ`.
--
--   **Finite sets of places.** $S_L$ is a finite set of primes of $\mathcal{O}_L$ satisfying `hSL`: every $w$ with $e(w \mid w \cap \mathcal{O}_K) \ne 1$ (in the form `(HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1`) lies in $S_L$. $S$ and $T$ are finite sets of primes of $\mathcal{O}_K$, with `hT`: for $v \in T$, no prime $w$ of $\mathcal{O}_L$ lying over $v$ belongs to $S_L$. The finite set $S_\tau$ is characterised by `hSτ`: $v \in S_\tau$ if and only if either ($v \in S$ and $v \notin T$) or there is a prime $w$ over $v$ with $e(w \mid v) \ne 1$.
--
--   **Local data.** For each prime $v$ of $\mathcal{O}_K$, `ws v` is a chosen prime of $\mathcal{O}_L$ over $v$, `ns v` a natural number, `rTs v` a family of `ns v` elements of $\mathrm{GL}_2(L_{\mathrm{ws}\,v})$ and `zs v` an element of that group; $\varphi_a$ is a function on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ and $\varphi_S$ a family of functions on the groups $\mathrm{GL}_2(L \otimes_K K_v)$.
--
--   **Transversal data.** Given $n$, a family $c : \mathrm{Fin}\,n \to \mathbb{R}$, measures $\tau_j$ on $\mathbb{A}_L^\times$ (for the Borel structure [`NumberField.Idele.ideleBorel L`](def/NumberField_IdeleProductMeasure.html#L384)), measures $\tau^{\mathrm{fin}}_{j,v}$ on $(L \otimes_K K_v)^\times$, measures $\tau^{\mathrm{arch}}_{j,v}$ on $\bigl(\prod_{w \mid v} L_w\bigr)^\times$ and elements $\pi_{j,v} \in (L \otimes_K K_v)^\times$, the following hypotheses are imposed: `hcpos`, $c_j > 0$; `hlev`, $\tau_j$ gives measure zero to the set where the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) differs from $c_j$; `hτfin`, each $\tau_j$ is finite on compact sets; `hτ0`, $\tau_j$ gives measure zero to the complement of [`AutomorphicForm.TransversalMeasure.saturated K L Sτ`](def/AutomorphicForm_TransversalMeasure.html#L89), the set of ideles $t$ whose $v$-semi-local component `semiLocalIdele K L v t` lies, for every $v \notin S_\tau$, in the product of the integral units subgroup `integralUnits K L v` (the units of the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`) with the range of `includeUnits K L v`; `hgood`, for $v \notin S_\tau$ the measure $\tau^{\mathrm{fin}}_{j,v}$ is a Haar measure on $(L \otimes_K K_v)^\times$ restricted to `integralUnits K L v` and normalised by the reciprocal of the measure of that subgroup; `hgood'`, for $v \notin S_\tau$ the measure $\tau^{\mathrm{fin}}_{j,v}$ vanishes off `integralUnits K L v` and gives it mass $1$; `hbad`, for $v \in S_\tau$ the measure $\tau^{\mathrm{fin}}_{j,v}$ is the translate by $\pi_{j,v}$ of the image, under the inclusion, of a Haar measure on `normOneUnits K L v`, the kernel of the valuation composed with the norm $L \otimes_K K_v \to K_v$; `harch`, each $\tau^{\mathrm{arch}}_{j,v}$ is the image under the inclusion of a Haar measure on `archNormOneUnits K L v`, the kernel of the absolute value composed with the norm to $K_v$; and `hfac3`, for every $j$ and every finite set $S_f \supseteq S_\tau$ of primes of $\mathcal{O}_K$, every family $f_v$ of $[0,\infty]$-valued functions on $(L \otimes_K K_v)^\times$ measurable for $v \in S_f$ and every family $g_v$ of measurable $[0,\infty]$-valued functions on the archimedean semi-local unit groups,
--   $$\int^- \Bigl(\prod_{v \mid \infty} g_v(\mathrm{arch}_v t)\Bigr)\Bigl(\prod_{v \in S_f} f_v(\mathrm{sl}_v t)\Bigr)\mathbf{1}\{\,\mathrm{sl}_v t \in \text{integral units for all } v \notin S_f\,\}\, d\tau_j(t) = \prod_{v\mid\infty}\Bigl(\int^- g_v\, d\tau^{\mathrm{arch}}_{j,v}\Bigr)\prod_{v \in S_f}\Bigl(\int^- f_v\, d\tau^{\mathrm{fin}}_{j,v}\Bigr),$$
--   where $\mathrm{arch}_v$ and $\mathrm{sl}_v$ are `archSemiLocalIdele K L v` and `semiLocalIdele K L v`.
--
--   **Conclusion.** For all families of natural numbers $k_\bullet, j_\bullet$ indexed by the primes of $\mathcal{O}_K$, every $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ and every $\varphi_f : \mathrm{GL}_2(\mathbb{A}_{L,\mathrm{fin}}) \to \mathbb{C}$ such that `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` holds for the family of local factors which at $v \in T$ is
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\text{semiLocalIntegralSet}\,K\,L\,v}\bigl(\gamma_{v,\iota}^{-1} x\bigr), \qquad \gamma_{v,\iota} = \mathrm{semiLocalComponent}_v\Bigl(\mathrm{localEmbed}_{\mathrm{ws}\,v}\bigl(\textstyle\prod_{m} rT_v(\iota\, m) \cdot (z_v)^{j_v}\bigr)\Bigr),$$
--   the product being taken in the order $m = 0, 1, \dots, k_v - 1$, and which at $v \notin T$ is $\varphi_S(v)$ — so that: $\varphi_a$ is an archimedean test factor (compactly supported and of the form $\Phi \circ \mathrm{archEntries}$ for a smooth $\Phi$), $\varphi_f$ is locally constant with compact support, each local factor at $v \in S \cup T$ is locally constant with compact support, $\varphi_f(h) = \prod_{v \in S \cup T} (\text{local factor})_v(\mathrm{semiLocalComponent}_v h)$ whenever all components of $h$ off $S \cup T$ lie in `semiLocalIntegralSet K L v` (the set of $g$ with $g$ and $g^{-1}$ having entries in the image of `tensorAdicCompletionIntegersTo`), $\varphi_f(h) = 0$ if some component off $S\cup T$ fails this, and $\varphi(g) = \varphi_a(\mathrm{glArch}\, g)\,\varphi_f(\mathrm{glFin}\, g)$ — the following holds for every $j \in \mathrm{Fin}\,n$, every $y \in \mathbb{A}_K^\times$ and every $\theta \in \mathbb{R}$.
--
--   Write, for $t, \zeta \in \mathbb{A}_L^\times$ and $k \in$ `adelicMaximalCompact L`,
--   $$F_{t,k,\zeta}(w) = \varphi\bigl(k^{-1}\, n(w\,t^{-1})\, d(\sigma_D(t)\,t^{-1})\, z(\sigma_D(\zeta))\, \sigma_D(k)\bigr), \qquad w \in \mathbb{A}_L,$$
--   where $n(x) = \mathrm{unipotentGL2}(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, $d(a) = \mathrm{diagOne}(a) = \mathrm{diag}(a,1)$, $z(a) = \mathrm{centralScalar}(a)$ is the scalar matrix, $\sigma_D$ is `unitsAct D σ` on ideles and `sigmaAdelicAct K L D σ` on $\mathrm{GL}_2(\mathbb{A}_L)$; and let $\Phi_{t,k,\zeta} =$ `tracePushforward K L` $F_{t,k,\zeta}$, the function on $\mathbb{A}_K$ whose value at $r$ is the integral of $F_{t,k,\zeta}$ over the parametrised trace fibre `traceFibre K L r`, namely $\mathrm{genuine}\beta(r)\,[L:K]^{-1} + \sum_i \mathrm{genuine}\beta(w_i)\,b_i$ with $b_i$ the chosen basis of $\ker(\mathrm{Tr}_{L/K})$, with respect to the product of copies of the adelic additive Haar measure of $K$. Finally let $|y| =$ [`NumberField.TateGlobal.ideleNorm K y`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of $\mathbb{A}_K$ at $y$.
--
--   The first conjunct asserts absolute convergence in the iterated sense: the iterated lower integral
--   $$\int^-\!\!\int^-\!\!\int^- \Bigl\| \xi_L(\zeta)\Bigl( \sum_{\eta \in K^\times}^{\mathrm{f}} \Phi_{t,k,\zeta}\bigl(\eta\, y^{-1}\bigr) - \bigl[\theta < |y|\bigr]\,|y| \int_{\mathbb{A}_K} \Phi_{t,k,\zeta}(u)\, d\mu_K(u)\Bigr)\Bigr\|_{\mathrm{e}}\, d\nu_{Z_L}(\zeta)\, dk\, d\tau_j(t)$$
--   is not $\infty$; here $\sum^{\mathrm{f}}$ is the finsum over $\eta \in K^\times$, the argument $\eta y^{-1}$ means $\mathrm{algebraMap}_{K \to \mathbb{A}_K}(\eta)\cdot y^{-1}$, and $[\theta < |y|]$ denotes the case distinction which contributes the displayed term if $\theta < |y|$ and $0$ otherwise.
--
--   The second conjunct asserts the interchange:
--   $$\int\!\!\int\!\!\int \xi_L(\zeta)\Bigl( \sum_{\eta \in K^\times}^{\mathrm{f}} \Phi_{t,k,\zeta}(\eta y^{-1}) - \bigl[\theta < |y|\bigr]\,|y|\int_{\mathbb{A}_K}\Phi_{t,k,\zeta}\, d\mu_K\Bigr) d\nu_{Z_L}\, dk\, d\tau_j$$
--   equals
--   $$\sum_{\eta \in K^\times}^{\mathrm{f}} \Bigl(\int\!\!\int\!\!\int \xi_L(\zeta)\,\Phi_{t,k,\zeta}(\eta y^{-1})\, d\nu_{Z_L}\, dk\, d\tau_j\Bigr) - \bigl[\theta < |y|\bigr]\,|y| \int_{\mathbb{A}_K} \Bigl(\int\!\!\int\!\!\int \xi_L(\zeta)\,\Phi_{t,k,\zeta}(u)\, d\nu_{Z_L}\, dk\, d\tau_j\Bigr) d\mu_K(u),$$
--   all iterated integrals being taken in the order $\zeta$ (against $\nu_{Z_L}$), then $k$ (against `maximalCompactHaar L`), then $t$ (against $\tau_j$), and all Bochner integrals being understood in Lean's convention, so that a non-integrable integrand contributes $0$.
--
--   This is the interchange step for the unipotent-type term of the twisted trace formula of a cyclic extension $L/K$: the sum over $K^\times$ and the subtraction of the truncated constant term may be moved outside the triple integral over the transversal, the maximal compact subgroup and the central ideles, together with the absolute convergence that licenses it. It is used in the assembly of that term, [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_indicator_prod_twistedLocalFactor_sub_unram), whose other ingredient identifies the resulting transversal integrals as products of local twisted factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram.lean

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

theorem AutomorphicForm.TwistedBruhat.forall_integral_transversal_finsum_tracePushforward_sub_eq_finsum_integral_transversal_sub_unram
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
            ((∑ᶠ η : Kˣ, (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) ∂νZL)
              ∂(maximalCompactHaar L) ∂(τ j))) -
              (if θ < NumberField.TateGlobal.ideleNorm K y then
                ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂νZL)
              ∂(maximalCompactHaar L) ∂(τ j)) ∂μK else 0)) := by sorry
