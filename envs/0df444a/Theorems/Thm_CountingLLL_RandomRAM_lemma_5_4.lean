-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_lemma_5_4
-- name    : CountingLLL.RandomRAM.lemma_5_4
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:58:27.911066+00:00
-- url     : https://prove2.me/theorems/7fa28889-0c93-47d6-85dc-1f4a034255a2
-- title:
--   Zero-terminated reciprocal series (Lemma 5.4)
-- statement:
--   Let independent copies of a measurable random state have a real value Y and a nonnegative extended-real sampling cost K, allowing arbitrary dependence between Y and K within a single copy. Suppose Y is square-integrable, its mean r lies in [0,1), its second moment M is below 1, and tau=Pr[Y!=0]<1. Form P_0=1, P_n=Y_1...Y_n, and stop at the first zero. Then termination is almost sure; the infinite prefix-product sum W agrees with the finite stopped sum; W and W^2 are integrable with E[W]=1/(1-r) and E[W^2]=(1+r)/((1-r)(1-M)); the expected number of samples is 1/(1-tau); and the expected total sampling cost, including the zero draw, is E[K]/(1-tau). Samples are modeled on the countable IID product space, and nonnegative cost expectations use extended-real conventions.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.4 and equation (27), Section 5.2.1, PDF p.18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.lemma_5_4 {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (Y : β → ℝ) (K : β → ℝ≥0∞) (hY : Measurable Y) (hK : Measurable K)
    (hY2 : MemLp Y 2 ν)
    (hr0 : 0 ≤ ∫ x, Y x ∂ν) (hr1 : (∫ x, Y x ∂ν) < 1)
    (hM : (∫ x, (Y x)^2 ∂ν) < 1) (hτ : ν {x | Y x ≠ 0} < 1) :
    let μ : Measure (ℕ → β) := Measure.infinitePi fun _ : ℕ => ν
    let r : ℝ := ∫ x, Y x ∂ν
    let M : ℝ := ∫ x, (Y x)^2 ∂ν
    let τ : ℝ≥0∞ := ν {x | Y x ≠ 0}
    let W : (ℕ → β) → ℝ := fun ω => ∑' n : ℕ, ∏ k ∈ Finset.range n, Y (ω k)
    let S : ℕ → Set (ℕ → β) := fun n => {ω | ∀ i < n, Y (ω i) ≠ 0}
    (∀ᵐ ω ∂μ, ∃ k, Y (ω k) = 0) ∧
    (∀ (ω : ℕ → β) (k : ℕ), Y (ω k) = 0 →
      W ω = ∑ n ∈ Finset.range (k+1), ∏ j ∈ Finset.range n, Y (ω j)) ∧
    Integrable W μ ∧ (∫ ω, W ω ∂μ) = (1-r)⁻¹ ∧
    Integrable (fun ω => (W ω)^2) μ ∧
    (∫ ω, (W ω)^2 ∂μ) = (1+r)/((1-r)*(1-M)) ∧
    (∫⁻ ω, ∑' n : ℕ, (S n).indicator (1 : (ℕ → β) → ℝ≥0∞) ω ∂μ) = (1-τ)⁻¹ ∧
    (∫⁻ ω, ∑' n : ℕ, (S n).indicator (fun ω => K (ω n)) ω ∂μ) =
      (∫⁻ x, K x ∂ν) / (1-τ) := by sorry
