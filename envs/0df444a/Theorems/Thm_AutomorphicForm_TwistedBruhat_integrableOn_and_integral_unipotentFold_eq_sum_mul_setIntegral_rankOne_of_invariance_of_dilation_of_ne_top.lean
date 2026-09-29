-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
-- name    : AutomorphicForm.TwistedBruhat.integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/b89be1e5-3371-5cd2-b601-48b59f19fb89
-- title:
--   Transversal descent of the unipotent fold to rank-one integrals
-- statement:
--   Throughout, $K \subseteq L$ is an extension of number fields with $L/K$ Galois, $\sigma \in \mathrm{Gal}(L/K)$, and $D$ is an idelic Galois descent datum for $L/K$, i.e. a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ whose value on each $g$ is continuous and restricts on $L$ to $g$; [`M4aHerbrand.IdeleGaloisDescent.unitsAct D σ`](def/M4aHerbrand_IdeleClassVocab.html#L41) denotes the induced automorphism of the idele group $\mathbb{A}_L^\times$, and [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$. The idele group of $L$ carries a declared measurable structure with the associated Borel property, together with a Haar measure $\nu_{Z,L}$ on it; the $t$-integrals use instead the Borel structure [`NumberField.Idele.ideleBorel`](def/NumberField_IdeleProductMeasure.html#L384) and the Haar measure [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391), and $\mu_K$ is an additive Haar measure on $\mathbb{A}_K$. Further data: a character $\xi_L$ of the whole idele group of $L$, presented as a homomorphism on the top subgroup, such that $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous; a continuous function $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ with compact support; and a real number $R$.
--
--   For $t, \zeta \in \mathbb{A}_L^\times$ and $k$ in `adelicMaximalCompact L` (the subgroup of $g \in \mathrm{GL}_2(\mathbb{A}_L)$ whose finite part is integral of level $\top$ and each of whose archimedean components is a row isometry, equipped with its Haar measure `maximalCompactHaar L`), write
--   $$\Phi_{t,k,\zeta}(w) \;=\; \varphi\Bigl(k^{-1}\, u(w t^{-1})\, \mathrm{diag}(\sigma_D(t)t^{-1},1)\, z(\sigma_D(\zeta))\, \sigma_D(k)\Bigr), \qquad w \in \mathbb{A}_L,$$
--   where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ is `unipotentGL2`, $\mathrm{diag}(a,1)$ is `diagOne`, $z$ is the central scalar embedding `centralScalar`, $\sigma_D =$ `unitsAct D σ` on ideles and `sigmaAdelicAct K L D σ` on $\mathrm{GL}_2$. Let $\Phi^\flat =$ `tracePushforward K L` $\Phi$ denote the adelic trace pushforward, $\Phi^\flat(r) = \int \Phi(\mathrm{traceFibre}\,K\,L\,r\,w)\,dw$ against the product additive Haar measure on $\mathbb{A}_K^{\,\mathrm{finrank}_K \ker(\mathrm{Tr}_{L/K})}$. Write $|\cdot|_L$, $|\cdot|_K$ for [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) (the module of the scaling action on the adele ring), $\mathrm{ht}$ for [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), $\mathrm{bc}$ for [`AutomorphicForm.TransversalMeasure.idelesBaseChange K L`](def/AutomorphicForm_TransversalMeasure.html#L85) (the map on units induced by the adelic base change ring map), and $\iota : K^\times \to \mathbb{A}_K^\times$ for the map induced by $K \to \mathbb{A}_K$. Finally set
--   $$F(t) \;=\; |t|_L^{-1}\int_{k}\Bigl(\int_{\zeta} \xi_L(\zeta)\Bigl(\sum^{\flat}_{\eta \in K^\times} \Phi^\flat_{t,k,\zeta}(\eta) - \mathbf 1[\,e^{R} < \mathrm{ht}(\mathrm{diag}(t,1))\,]\int_{\mathbb{A}_K} \Phi^\flat_{t,k,\zeta}\,d\mu_K\Bigr) d\nu_{Z,L}(\zeta)\Bigr) dk ,$$
--   the sum over $\eta$ being the `∑ᶠ` finite-support sum of $\Phi^\flat_{t,k,\zeta}$ evaluated at the images of $\eta$ in $\mathbb{A}_K$.
--
--   The hypotheses fall into the following groups. Transversal data: a finite set $S_\tau$ of height-one primes of $\mathcal{O}_K$, an integer $n$, reals $c_j > 0$ and $a_j$ ($j \in \mathrm{Fin}\,n$) and a real $b$, measures $\tau_j$ on the idele group of $L$ (for `ideleBorel L`), and a constant $c_\tau \in [0,\infty]$ with $c_\tau \neq 0$ and $c_\tau \neq \infty$, subject to: $\tau_j\{t : |t|_L \neq c_j\} = 0$; each $\tau_j$ is finite on compacts; the saturated set $\mathrm{sat} =$ [`AutomorphicForm.TransversalMeasure.saturated K L Sτ`](def/AutomorphicForm_TransversalMeasure.html#L89) $= \{t : \mathrm{semiLocalIdele}_v(t) \in \mathrm{saturatedUnits}_v$ for all $v \notin S_\tau\}$ is measurable and stable under multiplication by $\mathrm{bc}(s)$ for every $s \in \mathbb{A}_K^\times$; $\tau_j(\mathrm{sat}^{c}) = 0$ for all $j$; and the transversality identity `hτ2`: for every measurable $E \subseteq \mathrm{sat}$ the function $s \mapsto (\sum_j \tau_j)(E\,\mathrm{bc}(s)^{-1})$ is measurable and $\mathrm{idelicHaar}_L(E) = c_\tau \int^{-} (\sum_j \tau_j)(E\,\mathrm{bc}(s)^{-1})\, d\,\mathrm{idelicHaar}_K(s)$. Fundamental domains: a measurable set $\Omega_2^K$ in the ideles of $L$ which is a fundamental domain for the range of $\mathrm{bc} \circ \iota$ acting on $\mathbb{A}_L^\times$ with $\mathrm{idelicHaar}_L$, and a set $\Omega_K$ which is a fundamental domain for the range of $\iota$ in $\mathbb{A}_K^\times$ with $\mathrm{idelicHaar}_K$. Threshold comparison `hthr`: for each $j$, each $t$ with $|t|_L = c_j$ and each $y \in \mathbb{A}_K^\times$, the inequality $e^{R} < \mathrm{ht}(\mathrm{diag}(t\,\mathrm{bc}(y),1))$ holds if and only if $a_j e^{bR} < |y|_K$. Descent compatibility `hDbc`: $\sigma_D(\mathrm{bc}(y)) = \mathrm{bc}(y)$ for all $y \in \mathbb{A}_K^\times$. Support `hsupp`: $\Phi_{t,k,\zeta}(w) = 0$ for all $k$, $\zeta$, $w$ whenever $t \notin \mathrm{sat}$. Finiteness `hfinJ`: the iterated lower integral
--   $$\int^{-}_{t \in \Omega_2^K}\int^{-}_{k}\int^{-}_{\zeta}\;\|\xi_L(\zeta)\|_e \cdot \Bigl\|\sum^{\flat}_{\eta \in K^\times}\Phi^\flat_{t,k,\zeta}(\eta) - \mathbf 1[\,e^{R} < \mathrm{ht}(\mathrm{diag}(t,1))\,]\int \Phi^\flat_{t,k,\zeta}\,d\mu_K\Bigr\|_e \cdot |t|_L^{-1}$$
--   against $\nu_{Z,L}$, then $\mathrm{maximalCompactHaar}_L$, then $\mathrm{idelicHaar}_L$, is not $\infty$. Invariance `hINV`: $F(t\,\mathrm{bc}(\iota q)) = F(t)$ for all $q \in K^\times$ and all $t$. Dilation `hDIL`: for all $t \in \mathbb{A}_L^\times$ and $y \in \mathbb{A}_K^\times$,
--   $$F(t\,\mathrm{bc}(y)) = |t|_L^{-1}|y|_K^{-1}\int_k \int_\zeta \xi_L(\zeta)\Bigl(\sum^{\flat}_{\eta \in K^\times}\Phi^\flat_{t,k,\zeta}(\eta y^{-1}) - \mathbf 1[\,e^{R} < \mathrm{ht}(\mathrm{diag}(t\,\mathrm{bc}(y),1))\,]\,|y|_K\int \Phi^\flat_{t,k,\zeta}\,d\mu_K\Bigr) d\nu_{Z,L}\,dk,$$
--   the inner functions $\Phi_{t,k,\zeta}$ on the right being formed with $t$ itself. Measurability `hMEAS`: $F$ is measurable for `ideleBorel L`.
--
--   Under these hypotheses, writing for each $j$
--   $$H_j(y) \;=\; |y|_K^{-1}\int_{t}\int_{k}\int_{\zeta} \xi_L(\zeta)\Bigl(\sum^{\flat}_{\eta \in K^\times}\Phi^\flat_{t,k,\zeta}(\eta y^{-1}) - \mathbf 1[\,a_j e^{bR} < |y|_K\,]\,|y|_K\int \Phi^\flat_{t,k,\zeta}\,d\mu_K\Bigr)\,d\nu_{Z,L}(\zeta)\,dk\,d\tau_j(t),$$
--   with the $|y|_K^{-1}$ and $|y|_K$ taken as complex scalars, two assertions hold.
--
--   First, for every $j \in \mathrm{Fin}\,n$ the function $H_j$ is integrable on $\Omega_K$ with respect to $\mathrm{idelicHaar}_K$.
--
--   Secondly,
--   $$\int_{\Omega_2^K} F(t)\, d\,\mathrm{idelicHaar}_L(t) \;=\; \sum_{j} \bigl(c_\tau^{\mathrm{toReal}}\, c_j^{-1}\bigr)\int_{\Omega_K} H_j(y)\, d\,\mathrm{idelicHaar}_K(y),$$
--   where the left-hand integrand is exactly $F$ as written above, namely the iterated integral over $k$ and $\zeta$ of $\xi_L(\zeta)$ times the difference of the $K^\times$-sum and the $\mu_K$-integral cut off by $e^{R} < \mathrm{ht}(\mathrm{diag}(t,1))$, multiplied by the real scalar $|t|_L^{-1}$, and the scalars $c_\tau^{\mathrm{toReal}} c_j^{-1}$ are regarded as complex numbers.
--
--   This is the assembly step that descends the $\sigma$-twisted unipotent fold, integrated over a fundamental domain for the base-changed idele classes of $K$ inside those of $L$, to a finite sum of rank-one integrals over a fundamental domain $\Omega_K$ in the idele classes of $K$, with the height cut-off $e^R$ converted into the norm thresholds $a_j e^{bR}$. It is the final input to [`AutomorphicForm.TwistedBruhat.integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal`](thm.html#AutomorphicForm.TwistedBruhat.integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal), and uses the transversality identity in its quotient form supplied by [`AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal`](thm.html#AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (Ω₂K : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₂Km : @MeasurableSet _ (NumberField.Idele.ideleBorel L) Ω₂K)
    (hΩ₂K : @IsFundamentalDomain
      ((AutomorphicForm.TransversalMeasure.idelesBaseChange K L).comp
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₂K (NumberField.Idele.idelicHaar L))
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure]

    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (c : Fin n → ℝ)
    (τ : Fin n → @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)) (cτ : ℝ≥0∞)
    (hcτ0 : cτ ≠ 0) (hcτT : cτ ≠ ⊤) (hcpos : ∀ j, 0 < c j)
    (hlev : ∀ j, τ j {t | NumberField.TateGlobal.ideleNorm L t ≠ c j} = 0)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j))
    (hmeas : @MeasurableSet (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)
      (AutomorphicForm.TransversalMeasure.saturated K L Sτ))
    (hmul : ∀ t ∈ AutomorphicForm.TransversalMeasure.saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ,
      t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s ∈ AutomorphicForm.TransversalMeasure.saturated K L Sτ)
    (hτ0 : ∀ j, τ j (AutomorphicForm.TransversalMeasure.saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, @MeasurableSet _ (NumberField.Idele.ideleBorel L) E →
      E ⊆ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      @Measurable _ _ (NumberField.Idele.ideleBorel K) _ (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ,
          (∑ j, τ j) ((fun t => t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))

    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : @IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range _ _ _
      (NumberField.Idele.ideleBorel K) ΩK (NumberField.Idele.idelicHaar K))

    (a : Fin n → ℝ) (b : ℝ)
    (hthr : ∀ (j : Fin n) (t : (AdeleRing (𝓞 L) L)ˣ), NumberField.TateGlobal.ideleNorm L t = c j →
      ∀ y : (AdeleRing (𝓞 K) K)ˣ,
        (Real.exp R < NumberField.AdelicHeight.adelicHeight L
            (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) ↔
          a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y))

    (hDbc : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
        AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)

    (hsupp : ∀ t : (AdeleRing (𝓞 L) L)ˣ, t ∉ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0)

    (hfinJ : ∫⁻ t in Ω₂K, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ * ‖((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0))‖ₑ *
          ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂νZL ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ≠ ⊤)

    (hINV : ∀ (q : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))

    (hDIL : ∀ (t : (AdeleRing (𝓞 L) L)ˣ) (y : (AdeleRing (𝓞 K) K)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y)⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      (((NumberField.TateGlobal.ideleNorm L t)⁻¹ * (NumberField.TateGlobal.ideleNorm K y)⁻¹ : ℝ) : ℂ) *
        ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) : AdelicGL2 (𝓞 L) L) then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L))

    (hMEAS : @Measurable (AdeleRing (𝓞 L) L)ˣ ℂ (NumberField.Idele.ideleBorel L) _
      (fun t : (AdeleRing (𝓞 L) L)ˣ => ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L))) :
    (∀ j : Fin n, IntegrableOn (fun y : (AdeleRing (𝓞 K) K)ˣ =>
        ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
          (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)))
        ΩK (NumberField.Idele.idelicHaar K)) ∧
    ∫ t in Ω₂K, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) =
      ∑ j : Fin n, ((cτ.toReal * (c j)⁻¹ : ℝ) : ℂ) * ∫ y in ΩK,
          ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ)⁻¹ *
            (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)))
                    (algebraMap K (AdeleRing (𝓞 K) K) (η : K) * ((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))) -
                  (if a j * Real.exp (b * R) < NumberField.TateGlobal.ideleNorm K y then
                    ((NumberField.TateGlobal.ideleNorm K y : ℝ) : ℂ) * ∫ u, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) u ∂μK
                  else 0)) ∂νZL) ∂(maximalCompactHaar L) ∂(τ j)) ∂(NumberField.Idele.idelicHaar K) := by sorry
