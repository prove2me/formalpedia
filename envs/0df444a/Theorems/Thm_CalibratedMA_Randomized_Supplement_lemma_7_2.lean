-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_7_2
-- name    : CalibratedMA.Randomized.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:31:30.287695+00:00
-- url     : https://prove2.me/theorems/7dc22255-a1f0-40a8-90c1-0d0f20786491
-- title:
--   Lemma 7.2 — Decoding signs from a predictor close to separated baselines
-- statement:
--   Let $R\ge2$, let real baselines $t_i$ obey $|t_i-t_j|\ge\Delta_t>0$ for $i
--   e j$, and fix signs $\theta_i\in\{-1,1\}$ and $\eta>0$ such that $t_i+\eta\theta_i\in[0,1]$. Let $D_\theta$ have uniform contexts on $[R]$ and Bernoulli labels with these means. For every deterministic predictor $p:[R]\to[0,1]$, write $\bar e=R^{-1}\sum_i|p_i-t_i|$. For every $0<r<\Delta_t/2$ and either fixed sign at ties, the decoder $\widehat\theta_i=\operatorname{sign}(p_i-t_i)$ satisfies
--   $$\frac{d_H(\widehat\theta,\theta)}{R}\le\frac{2\bar e}{r}+\frac{\mathrm{ECE}_{D_\theta}(p)}{\eta}.$$
--   The baselines need not belong to $[0,1]$; only the means for this fixed hidden vector must be valid. This decoding inequality supports Theorem 7.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: a deterministic predictor p → the published CMA or ECE applied to x ↦ dirac(p(x)); reason: the point mass is exactly a deterministic prediction, with no new error measure
--   - encoding: the uniform Bernoulli hard law and sign decoder with arbitrary ties → offsetData and signDecoder with either fixed tie sign; reason: both displayed terms and the exact factor 2 are retained; no baseline range hypothesis is added
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 37, Lemma 7.2 (PDF pp. 39)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 7.2, p.37: no range restriction on the baselines beyond valid label means. -/
theorem lemma_7_2 (R : ℕ) (hR : 2 ≤ R) (t : Fin R → ℝ)
    (Δt : ℝ) (hΔt : 0 < Δt) (hsep : ∀ i j, i ≠ j → Δt ≤ |t i - t j|)
    (θ : Fin R → ℝ) (hθ : ∀ i, IsSign (θ i)) (η : ℝ) (hη : 0 < η)
    (hμ : ∀ i, t i + η * θ i ∈ Set.Icc (0 : ℝ) 1)
    (p : Fin R → ℝ) (hp : IsDetPredictor p) (tie : ℝ) (htie : IsSign tie)
    (r : ℝ) (hr : 0 < r) (hrΔ : r < Δt / 2) :
    (hamming (signDecoder tie p t) θ : ℝ) / R ≤
      2 * baselineError p t / r + ECE (offsetData t η θ) (pointPredictor p) / η := by sorry

end CalibratedMA.Randomized.Supplement
