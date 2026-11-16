-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_6_4
-- name    : CalibratedMA.Randomized.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:29:17.268438+00:00
-- url     : https://prove2.me/theorems/5484a2aa-7841-481a-bd94-9090a02256f8
-- title:
--   Lemma 6.4 — Recovering hidden bits from a randomized predictor
-- statement:
--   There are positive universal constants $a,c$, with $a\le1/4$. For every integer $k\ge2$, put $x_i=i/k$, $b_i=1/4+x_i/2$ and $\Delta=a/k^2$. For $\theta\in\{0,1\}^k$, let $D_\theta$ have uniform contexts $x_i$ and Bernoulli means $b_i+\Delta\theta_i$. Let $Q$ be any admissible randomized predictor. The public decoder defined by nearest-baseline bins and the integrals of $(P-b_i)$, with no labels or hidden bits as inputs, satisfies
--   $$\mathrm{CMA}_{D_\theta}(Q;\{x\mapsto x\})\le c/k^2
--   \quad\Longrightarrow\quad d_H(\widehat\theta,\theta)\le k/5.$$
--   The same decoder works for every hidden vector. This is the recovery statement used for the calibration component of Theorem 6.1.
--
--   Differences from the source:
--   - encoding: a finite discrete domain [R] → Fin R, with source coordinate i represented by i.val+1; reason: finite relabeling preserves every statistical experiment, test and error
--   - encoding: public points x_i=i/k and singleton identity test → a relabeled Fin k law and the actual test contextPoint i=(i.val+1)/k; reason: the labeled laws and published CMA are preserved by this bijection
--   - encoding: there is a label-free decoder and positive universal a,c → the displayed public decoder bitDecoder and witnesses with a≤1/4; reason: the proof explicitly constructs this decoder and chooses a≤1/4; there is no hidden-vector input
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 34, Lemma 6.4 (PDF pp. 36)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Hidden

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 6.4, p.34, using the public decoder displayed immediately below the statement. -/
theorem lemma_6_4 :
    ∃ a c : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < c ∧
      ∀ k : ℕ, ∀ hk : 2 ≤ k, ∀ (Q : Fin k → Measure ℝ),
        IsRandomizedPredictor Q → ∀ θ : Fin k → ℝ, (∀ i, IsBit (θ i)) →
        CMA (offsetData baseline (a / (k : ℝ) ^ 2) θ) Q {contextPoint} ≤ c / (k : ℝ) ^ 2 →
        (hamming (bitDecoder k (by omega) (a / (k : ℝ) ^ 2) Q) θ : ℝ) ≤ (k : ℝ) / 5 := by sorry

end CalibratedMA.Randomized.Supplement
