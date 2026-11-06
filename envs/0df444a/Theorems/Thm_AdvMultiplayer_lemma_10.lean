-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_10
-- name    : AdvMultiplayer.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:53:07.958211+00:00
-- url     : https://prove2.me/theorems/18236eba-d388-46f3-a99b-86a7c495b791
-- title:
--   Lemma 10 — cost of parallel service
-- statement:
--   For a service phase with stopping times $1\le\sigma\le\vartheta\le T+1$, shrinking $\mathcal F_t$-measurable task sets $P_t\subseteq[d]$, empty outside the phase, service indicators $X_{i,t}\in\{0,1\}$ observable by round end, $J_{i,t}=\mathbf 1\{i\in P_t\}$ and $A_t=\mathbf 1\{\sigma\le t<\vartheta,P_t\ne\emptyset\}$: fix an integer $q\ge1$, $a>0$, and $\mathcal F_t$-measurable $\omega_t\in[0,K]$. Suppose the quota condition holds and $\mathbb E[X_{i,t}\mid\mathcal F_t]\ge a\omega_t$ on $\{J_{i,t}=1\}$. Then
--   $$\mathbb E\sum_{t=1}^TJ_{i,t}\omega_t\le\frac qa,\qquad\mathbb E\sum_{t=1}^TA_t\omega_t\le\frac{q+\log d}{(1-e^{-1})a},$$
--   and both bounds also hold conditional on $\mathcal F_\sigma$. Serving $d$ tasks in parallel costs an additive $\log d$, not a factor $d$.
--
--   Differences from the source:
--   - generalization: [d] with d = m - 1, K the number of arms, T the horizon → any d ≥ 1, any real K > 0 and any T; reason: the lemma does not involve the protocol and K enters only as a bound on ω_t, so taking d = m - 1, K the number of arms and T the horizon gives the source's statement
--   - encoding: A_t = 1{σ ≤ t < ϑ, P_t ≠ ∅} → 1{P_t ≠ ∅}; reason: P_t is empty outside the phase, so the two are equal
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 10, p.24, (22)

import Mathlib

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 10 (cost of parallel service).** Gan, arXiv:2610.05688, Lemma 10, p.24, (22), with the
setup of p.24: a service phase `σ ≤ t < ϑ` with stopping times `1 ≤ σ ≤ ϑ ≤ T+1`, `ℱ_t`-measurable
shrinking task sets `P_t ⊆ [d]`, empty outside the phase, indicators `X_{i,t} ∈ {0,1}` observable by
round end, `J_{i,t} = 1{i ∈ P_t}`, `A_t = 1{σ ≤ t < ϑ, P_t ≠ ∅}`, `N_i(v) = Σ_{t≤v} J_{i,t} X_{i,t}`.

All four bounds are stated: the task bound and (22), unconditionally and conditionally on `ℱ_σ`.

**Formalization Note.** The statement is abstract and independent of the protocol. `K` is any positive
bound on `ω_t`; `d ≥ 1`. -/
theorem lemma_10 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (d T q : ℕ) (hd : 1 ≤ d) (hq : 1 ≤ q) (a K : ℝ) (ha : 0 < a) (hK : 0 < K)
    (σ ϑ : Ω → ℕ) (hσ : IsStoppingTime ℱ fun x => ((σ x : ℕ) : WithTop ℕ))
    (hϑ : IsStoppingTime ℱ fun x => ((ϑ x : ℕ) : WithTop ℕ))
    (hphase : ∀ x, 1 ≤ σ x ∧ σ x ≤ ϑ x ∧ ϑ x ≤ T + 1)
    (P : ℕ → Ω → Finset (Fin d)) (hPm : ∀ t i, MeasurableSet[ℱ t] {x | i ∈ P t x})
    (hPoff : ∀ t x, ¬ (σ x ≤ t ∧ t < ϑ x) → P t x = ∅)
    (hPmono : ∀ t x, σ x ≤ t → t + 1 < ϑ x → P (t + 1) x ⊆ P t x)
    (X : Fin d → ℕ → Ω → ℝ) (hX01 : ∀ i t x, X i t x = 0 ∨ X i t x = 1)
    (hXm : ∀ i t, Measurable[ℱ (t + 1)] (X i t))
    (w : ℕ → Ω → ℝ) (hwm : ∀ t, Measurable[ℱ t] (w t)) (hwK : ∀ t x, 0 ≤ w t x ∧ w t x ≤ K)
    (hquota : ∀ i, ∀ t ∈ Finset.Icc 1 T, ∀ x, i ∈ P t x →
      ∑ s ∈ Finset.Icc 1 (t - 1), (if i ∈ P s x then X i s x else 0) < (q : ℝ))
    (hserve : ∀ i, ∀ t ∈ Finset.Icc 1 T, ∀ᵐ x ∂μ, i ∈ P t x → a * w t x ≤ (μ[X i t | ℱ t]) x) :
    (∀ i, ∫ x, (∑ t ∈ Finset.Icc 1 T, if i ∈ P t x then w t x else 0) ∂μ ≤ (q : ℝ) / a) ∧
    ∫ x, (∑ t ∈ Finset.Icc 1 T, if (P t x).Nonempty then w t x else 0) ∂μ
      ≤ ((q : ℝ) + Real.log d) / ((1 - Real.exp (-1)) * a) ∧
    (∀ i, (μ[fun x => ∑ t ∈ Finset.Icc 1 T, if i ∈ P t x then w t x else 0 | hσ.measurableSpace])
      ≤ᵐ[μ] fun _ => (q : ℝ) / a) ∧
    (μ[fun x => ∑ t ∈ Finset.Icc 1 T, if (P t x).Nonempty then w t x else 0 | hσ.measurableSpace])
      ≤ᵐ[μ] fun _ => ((q : ℝ) + Real.log d) / ((1 - Real.exp (-1)) * a) := by sorry

end AdvMultiplayer
