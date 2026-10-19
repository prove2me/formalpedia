-- Prove2me | Theorems.Thm_DynSetValue_DPP_lemma_3_10_i
-- name    : DynSetValue.DPP.lemma_3_10_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:12.368984+00:00
-- url     : https://prove2.me/theorems/d696c2a9-4a45-42e4-bbe2-3d1195dd0a0a
-- title:
--   Lemma 3.10(i) — discrete approximation of stopping data
-- statement:
--   Let $\tau$ be a stopping time and $\eta$ a bounded $\mathcal F_\tau$-measurable payoff vector. For every $\delta>0$ there are a finite-valued stopping time $\tau_\delta$ and a bounded, uniformly continuous $\mathcal F_{\tau_\delta}$-measurable payoff $\eta_\delta$ with the same bound as $\eta$, such that
--
--   $$
--   0\le\tau_\delta-\tau\le\delta,\qquad
--   \mathbb E^{\mathbb P_0}[\|\eta_\delta-\eta\|]\le\delta.
--   $$
--
--   The approximation provides regular terminal data for stopped games.
--
--   **Formalization Note** The expectation is encoded as a nonnegative extended integral to exclude a default-zero value on nonintegrable data.
-- source:
--   Feinstein, Rudloff, Zhang, Dynamic set values for nonzero sum games with multiple equilibriums, arXiv:2002.00449v2, p. 28, Lemma 3.10(i), equation (3.11)

import Mathlib
import Definitions.Def_DynSetValue_DPP_Setting
import Definitions.Def_DynSetValue_DPP_Game

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace DynSetValue.DPP

/-- Lemma 3.10(i), p. 28. -/
theorem lemma_3_10_i {T : ℝ} (hT : 0 < T) {d N : ℕ}
    (P0 : Measure (Ω T d)) (hP0 : IsWiener hT P0)
    (τ : Ω T d → WithTop ℝ) (hτ : IsStoppingTime (𝓕 hT P0) τ)
    (hτrange : ∀ ω, (0 : WithTop ℝ) ≤ τ ω ∧ τ ω ≤ (T : WithTop ℝ))
    (η : Ω T d → Payoff N) (hη : Measurable[hτ.measurableSpace] η)
    (C : ℝ) (hC : ∀ ω, ‖η ω‖ ≤ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (τδ : Ω T d → WithTop ℝ) (hτδ : IsStoppingTime (𝓕 hT P0) τδ)
      (ηδ : Ω T d → Payoff N),
      (Set.range τδ).Finite ∧
      (∀ ω, (0 : WithTop ℝ) ≤ τδ ω ∧ τδ ω ≤ (T : WithTop ℝ)) ∧
      (∀ ω, 0 ≤ stopTime τδ ω - stopTime τ ω ∧
        stopTime τδ ω - stopTime τ ω ≤ δ) ∧
      Measurable[hτδ.measurableSpace] ηδ ∧
      (∀ ω, ‖ηδ ω‖ ≤ C) ∧
      (∫⁻ ω : Ω T d, ENNReal.ofReal ‖ηδ ω - η ω‖ ∂P0) ≤ ENNReal.ofReal δ ∧
      UniformContinuous ηδ := by sorry

end DynSetValue.DPP
