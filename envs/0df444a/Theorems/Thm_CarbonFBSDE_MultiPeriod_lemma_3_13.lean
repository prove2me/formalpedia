-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_lemma_3_13
-- name    : CarbonFBSDE.MultiPeriod.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:25.966414+00:00
-- url     : https://prove2.me/theorems/648d6bb4-496c-4509-84cb-4a925f6e11d0
-- title:
--   Lemma 3.13, p. 24 — e ↦ v^Φ(t, p, e, e) is non-decreasing and tends to 0 as e → −∞
-- statement:
--   Let Assumption 1 hold, $r\in\mathbb R$, $\tau>0$, $\Phi\in\widehat{\mathcal K}$, and let $v^\Phi$ be the value function of Corollary 3.12. Then for every $t\in[0,\tau)$ and $p\in\mathbb R^d$ the function $e\mapsto v^\Phi(t,p,e,e)$ is non-decreasing and
--   $$\lim_{e\to-\infty}v^\Phi(t,p,e,e)=0.\tag{3.48}$$
--
--   The diagonal $v^\Phi(t,p,e,e)$ is the price when the cap parameter equals the current emission level; this lemma supplies the monotonicity and the lower limit needed for the next period's terminal condition to lie in $\widehat{\mathcal K}$ (Corollary 3.14).
--
--   **Formalization Note** "$v^\Phi$ given by Corollary 3.12" is the hypothesis that $v$ is a value function for $\Phi$ on $[0,\tau)$ (Model file).
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 24, Lemma 3.13, (3.48)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

theorem lemma_3_13 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (τ : ℝ≥0) (hτ : 0 < τ) (Φ : SDEState d → ℝ → ℝ → ℝ) (LΦ : ℝ) (hΦ : InKhat Φ LΦ)
    (v : ℝ≥0 → SDEState d → ℝ → ℝ → ℝ) (hv : IsValueFn B c r Φ τ v) :
    ∀ t < τ, ∀ p : SDEState d,
      Monotone (fun e => v t p e e) ∧ Tendsto (fun e => v t p e e) atBot (𝓝 0) := by sorry

end CarbonFBSDE.MultiPeriod
