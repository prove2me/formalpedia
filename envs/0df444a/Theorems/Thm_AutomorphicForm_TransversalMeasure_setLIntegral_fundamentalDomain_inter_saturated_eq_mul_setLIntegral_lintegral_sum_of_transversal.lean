-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
-- name    : AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/bca1c526-46fc-5158-9ef5-2ee3a8b66dce
-- title:
--   Transversal measure identity over a K^×-fundamental domain
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $S_\tau$ be a finite set of height-one primes of $\mathcal O_K$, let $\tau_0,\dots,\tau_{n-1}$ be measures on the idele unit group $(\mathbb A_L)^\times$, and let $c_\tau \in [0,\infty]$. Write $\mathrm{sat} =$ `saturated K L Sτ` for the set of ideles $t$ of $L$ such that for every prime $v \notin S_\tau$ of $\mathcal O_K$ the semi-local component `semiLocalIdele K L v t` lies in the product of the integral units with the image of `includeUnits K L v` inside $(L \otimes_K K_v)^\times$, and write $s \mapsto s_L$ for the monoid map `idelesBaseChange K L` induced by `genuineβ K L`. Assume: $\mathrm{sat}$ is measurable and stable under $t \mapsto t\, s_L$ for all $s \in (\mathbb A_K)^\times$; each $\tau_j$ is finite on compacts and vanishes on the complement of $\mathrm{sat}$; and for every measurable $E \subseteq \mathrm{sat}$ the function $s \mapsto (\sum_j \tau_j)(\{t : t\,s_L \in E\})$ is measurable with $$\mu_L(E) = c_\tau \int_{(\mathbb A_K)^\times} \Bigl(\sum_j \tau_j\Bigr)(\{t : t\,s_L \in E\})\, d\mu_K(s),$$ where $\mu_K =$ `idelicHaar K` and $\mu_L =$ `idelicHaar L` are the Haar measures for the Borel structures on the idele unit groups. Assume finally that $\Omega_K \subseteq (\mathbb A_K)^\times$ is a fundamental domain for the image of $K^\times$ with respect to $\mu_K$, and that $\Omega \subseteq (\mathbb A_L)^\times$ is a measurable fundamental domain for the image of $K^\times$ under $s \mapsto s_L$ with respect to $\mu_L$. The conclusion is the conjunction of two statements. First, for every measurable $G : (\mathbb A_L)^\times \to [0,\infty]$ with $G(t\,k_L) = G(t)$ for all $k \in K^\times$ and all $t$, $$\int_{\Omega \cap \mathrm{sat}} G \, d\mu_L = c_\tau \int_{\Omega_K} \int G(t\,s_L) \, d\Bigl(\sum_j \tau_j\Bigr)(t)\, d\mu_K(s).$$ Second, for every measurable $K^\times$-invariant $F : (\mathbb A_L)^\times \to \mathbb C$ whose upper integral of $\|F\|$ over $\Omega \cap \mathrm{sat}$ against $\mu_L$ is finite, the same identity holds for the Bochner integrals, with the constant read as the complex number attached to the real number $c_\tau$.
--
--   This is the quotient-by-$K^\times$ form of a transversality (Weil-type integration) identity: a disintegration of idelic Haar measure on $(\mathbb A_L)^\times$ along the base-changed torus $(\mathbb A_K)^\times$ and a finite family of transversal measures, transported to fundamental domains for $K^\times$ on both sides. It is used in the analysis of the unipotent term of a twisted Bruhat decomposition, and is cited by [`AutomorphicForm.TwistedBruhat.integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top`](thm.html#AutomorphicForm.TwistedBruhat.integrableOn_and_integral_unipotentFold_eq_sum_mul_setIntegral_rankOne_of_invariance_of_dilation_of_ne_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TransversalMeasure
open scoped ENNReal

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem AutomorphicForm.TransversalMeasure.setLIntegral_fundamentalDomain_inter_saturated_eq_mul_setLIntegral_lintegral_sum_of_transversal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Sτ : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (τ : Fin n → Measure (AdeleRing (𝓞 L) L)ˣ) (cτ : ℝ≥0∞)
    (hmeas : MeasurableSet (saturated K L Sτ))
    (hmul : ∀ t ∈ saturated K L Sτ, ∀ s : (AdeleRing (𝓞 K) K)ˣ, t * idelesBaseChange K L s ∈ saturated K L Sτ)
    (hτfin : ∀ j, IsFiniteMeasureOnCompacts (τ j)) (hτ0 : ∀ j, τ j (saturated K L Sτ)ᶜ = 0)
    (hτ2 : ∀ E : Set (AdeleRing (𝓞 L) L)ˣ, MeasurableSet E → E ⊆ saturated K L Sτ →
      Measurable (fun s : (AdeleRing (𝓞 K) K)ˣ =>
        (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)) ∧
      NumberField.Idele.idelicHaar L E = cτ *
        ∫⁻ s : (AdeleRing (𝓞 K) K)ˣ, (∑ j, τ j) ((fun t => t * idelesBaseChange K L s) ⁻¹' E)
          ∂(NumberField.Idele.idelicHaar K))
    (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK
      (NumberField.Idele.idelicHaar K))
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩm : MeasurableSet Ω)
    (hΩ : IsFundamentalDomain
      ((idelesBaseChange K L).comp (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K))).range Ω
      (NumberField.Idele.idelicHaar L)) :
    (∀ G : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞, Measurable G →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        G (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          G t) →
      ∫⁻ t in Ω ∩ saturated K L Sτ, G t ∂(NumberField.Idele.idelicHaar L) =
        cτ * ∫⁻ s in ΩK, ∫⁻ t, G (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) ∧
    (∀ F : (AdeleRing (𝓞 L) L)ˣ → ℂ, Measurable F →
      (∀ (k : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
        F (t * idelesBaseChange K L (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k)) =
          F t) →
      (∫⁻ t in Ω ∩ saturated K L Sτ, ‖F t‖ₑ ∂(NumberField.Idele.idelicHaar L) ≠ ⊤) →
      ∫ t in Ω ∩ saturated K L Sτ, F t ∂(NumberField.Idele.idelicHaar L) =
        (cτ.toReal : ℂ) *
          ∫ s in ΩK, ∫ t, F (t * idelesBaseChange K L s) ∂(∑ j, τ j) ∂(NumberField.Idele.idelicHaar K)) := by sorry
