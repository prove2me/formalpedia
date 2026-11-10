-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_lemma_3_6
-- name    : AgnosticImitate.Reduction.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:24:02.939207+00:00
-- url     : https://prove2.me/theorems/fbd97b9c-6a20-4fc6-9b7b-0943545aec43
-- title:
--   Lemma 3.6 — step sizes: uniform (1 + log T)/T, linear 4/(T + 1), geometric λ + (1 − λ)^T ≤ (1 + log T)/T
-- statement:
--   For weights $w_t$ let $W_t=w_1+\dots+w_t$ and $\delta=\sum_{t=1}^Tw_t^2/(W_tW_T)$. For every horizon $T\ge1$:
--
--   - **(Uniform)** if $w_t=1$ for all $t$, then $\delta\le(1+\log T)/T$;
--   - **(Linear)** if $w_t=t$ for all $t$, then $\delta\le4/(T+1)$;
--   - **(Geometric)** if $w_t\ge0$, $w_1>0$ and $w_t/W_t=\lambda$ for $2\le t\le T$, then $\delta=\lambda+(1-\lambda)^T$; for $\lambda=\log(T)/T$ this is at most $(1+\log T)/T$.
--
--   These imply the printed $\delta=O(\log(T)/T)$, $O(1/T)$ and $O(\log(T)/T)$.
--
--   Differences from the source:
--   - generalization: δ = O(log(T)/T) (uniform), δ = O(1/T) (linear), O(log(T)/T) (geometric) → for every T ≥ 1: δ ≤ (1 + log T)/T, δ ≤ 4/(T + 1), and δ = λ + (1 − λ)^T ≤ (1 + log T)/T; reason: the proof's explicit bounds imply the asymptotic ones; read for all T ≥ 1 the printed O(log(T)/T) would fail at T = 1 (log 1 = 0, δ = 1)
--   - generalization: geometric weights with λ = log(T)/T: δ = λ + (1 − λ)^T → the identity δ = λ + (1 − λ)^T for every λ with w_t/W_t = λ (2 ≤ t ≤ T); the bound for λ = log(T)/T; reason: the identity holds for every such λ; λ = log(T)/T is a special case
--   - encoding: geometric weights with w_t/W_t = λ → the extra hypothesis w_1 > 0; reason: the ratio and δ are undefined when W_1 = 0 (0/0); the source presupposes w_1 > 0, so only undefined cases are excluded
--   - encoding: weights w_1, …, w_T → weights w : ℕ → ℝ restricted to indices 1, …, T; uniform and linear weights supplied directly; reason: only the first T positive indices enter prefixW and stepDelta; no distribution means are used in this lemma
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Lemma 3.6, pp. 20–21 (PDF 22–23); explicit bounds from its proof, pp. 41–42 (PDF 43–44)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Losses

namespace AgnosticImitate.Reduction

/-- Lemma 3.6 (Step Sizes, pp. 20–21, PDF 22–23), with the explicit bounds of its proof
(pp. 41–42, PDF 43–44) for every horizon `T ≥ 1`, where `δ = Σ_{t=1}^T w_t² / (W_t W_T)`:
* (Uniform) `w_t = 1`: `δ ≤ (1 + log T)/T`;
* (Linear) `w_t = t`: `δ ≤ 4/(T + 1)`;
* (Geometric) `w_t ≥ 0`, `w_1 > 0` and `w_t / W_t = λ` for `2 ≤ t ≤ T`: `δ = λ + (1 - λ)^T`, and
  for `λ = log(T)/T` this is at most `(1 + log T)/T`. -/
theorem lemma_3_6 (T : ℕ) (hT : 1 ≤ T) :
    stepDelta (fun _ => 1) T ≤ (1 + Real.log T) / T ∧
    stepDelta (fun t => (t : ℝ)) T ≤ 4 / ((T : ℝ) + 1) ∧
    ∀ (w : ℕ → ℝ) (lam : ℝ), (∀ t ∈ Finset.Icc 1 T, 0 ≤ w t) → 0 < w 1 →
      (∀ t ∈ Finset.Icc 2 T, w t / prefixW w t = lam) →
      stepDelta w T = lam + (1 - lam) ^ T ∧
        (lam = Real.log T / T → stepDelta w T ≤ (1 + Real.log T) / T) := by sorry

end AgnosticImitate.Reduction
