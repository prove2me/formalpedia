-- Prove2me | Theorems.Thm_AsyncSA_Contraction_lemma2
-- name    : AsyncSA.Contraction.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:47.963692+00:00
-- url     : https://prove2.me/theorems/abafdb98-3b9c-4c2d-bdf1-cb58c13f4369
-- title:
--   Lemma 2 — uniform smallness of late noise tails
-- statement:
--   Under the scalar filtration, step-size, and conditional-noise conditions of Lemma 1, define the zero-start tail $W(t;t_0)$ by $W(t_0;t_0)=0$ and $W(t+1;t_0)=(1-\alpha(t))W(t;t_0)+\alpha(t)w(t)$ for $t\ge t_0$. Almost surely, for every $\delta>0$, there is a time $T$ such that
--
--   $$|W(t;t_0)|\le\delta\qquad\text{whenever }T\le t_0\le t.$$
--
--   The uniformity in both the starting and ending times lets later arguments restart the noise recursion after delayed information has become sufficiently recent.
--
--   **Formalization Note** On p. 192 the paper states this for the rescaled noise $\widetilde w_i(t)=w_i(t)/G(t)$. The preceding page establishes that the rescaled process satisfies Lemma 1's conditions; this statement records the same conclusion for any scalar process satisfying those conditions. The tail is zero before its start time as well.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), pp. 191–192, §4, rescaled noise and Lemma 2

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

/-- Lemma 2, p. 192, for any scalar noise process satisfying Lemma 1's conditions. -/
theorem lemma2 {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (α w B : ℕ → Ω → ℝ) (C : ℝ)
    (hαmeas : ∀ t, Measurable[𝓕 t] (α t))
    (hwmeas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t))
    (hmean : ∀ t, CondMeanZero m₀ (𝓕 t) P (w t))
    (hsq : ∀ t, CondSqLe m₀ (𝓕 t) P (w t) (B t))
    (hαmem : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : ∀ᵐ ω ∂P,
      Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (hsum : ∀ᵐ ω ∂P,
      ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hBbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
        |tailW (fun s => α s ω) (fun s => w s ω) t₀ t| ≤ δ := by sorry

end AsyncSA.Contraction
