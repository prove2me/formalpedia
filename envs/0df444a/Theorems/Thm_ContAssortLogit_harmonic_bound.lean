-- Prove2me | Theorems.Thm_ContAssortLogit_harmonic_bound
-- name    : ContAssortLogit.harmonic_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:34:25.753458+00:00
-- url     : https://prove2.me/theorems/76e120d1-e143-4d9b-9e49-a26ffc99e195
-- title:
--   App. A.1, p.36 — $\sum_{t=1}^T(t+\beta)^{-1}\le3\log T$ for $T\ge2$
-- statement:
--   For every $\beta\ge0$ and every integer $T\ge2$,
--   $$\sum_{t=1}^T\frac{1}{t+\beta}\le3\log T.$$
--
--   This closes the regret bound: summing the rate $\kappa/(t+\beta)$ of Lemma 5 over the horizon costs a logarithmic factor.
--
--   Differences from the source:
--   - generalization: $\beta\ge\max\{0,\alpha-1\}$ (the policy's parameter) → every $\beta\ge0$; reason: the bound uses only $\beta\ge0$; the paper's $\beta$ is a special case
--   - reading: $\log T$ → the natural logarithm $\ln T$; reason: the paper gives no base; the natural logarithm is the convention of the paper's analysis and the strongest of the usual readings
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, App. A.1, p.36, "by ∑_{t=1}^T (t + β)⁻¹ ⩽ 3 log T for all T ⩾ 2"

import Mathlib
open MeasureTheory Set

namespace ContAssortLogit

/-- **The harmonic bound** (Peeters, den Boer & Mandjes, arXiv:1807.06497v4, App. A.1, p.36):
`Σ_{t=1}^T (t + β)⁻¹ ≤ 3 log T` for all `T ≥ 2`, for every `β ≥ 0`. -/
theorem harmonic_bound (β : ℝ) (hβ : 0 ≤ β) (T : ℕ) (hT : 2 ≤ T) :
    ∑ t ∈ Finset.Icc 1 T, 1 / ((t : ℝ) + β) ≤ 3 * Real.log T := by sorry

end ContAssortLogit
