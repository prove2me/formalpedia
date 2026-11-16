-- Prove2me | Theorems.Thm_AMRangeAvoid_Characterization_Supplement_lemma_2_15
-- name    : AMRangeAvoid.Characterization.Supplement.lemma_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:27:59.257581+00:00
-- url     : https://prove2.me/theorems/72c60972-827a-4cd4-9673-7cf9d21b6a1d
-- title:
--   Lemma 2.15 — The complete finite-grid ball overlap inequality
-- statement:
--   Let $n\ge1$, let $R$ be an integer with $R>\sqrt n/2$, and put $r_-=R-\sqrt n/2$ and $r_+=R+\sqrt n/2$. For $w\in\mathbb Z^n$ with $\|w\|_2\le2r_-$, let $E_R=\{z\in\mathbb Z^n:\|z\|_2\le R\}$. Then
--
--   $$\frac{|E_R\cap(E_R+w)|}{|E_R|}\ge\frac1{\sqrt{2\pi n}}\left(\frac{r_-}{r_+}\right)^n\left(1-\frac{\|w\|_2^2}{4r_-^2}\right)^{(n+1)/2}.$$
--
--   The bound retains the exact constant and exponent and applies to every admissible radius and integer translation, including the boundary $\|w\|_2=2r_-$.
--
--   Differences from the source:
--   - encoding: integer Euclidean balls in positive dimension → finite sets of vectors on Fin n defined by exact sums of squared coordinates; reason: this is the same closed Euclidean ball, with the positive-dimension convention inherited from Lemma 2.14
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Lemma 2.15, printed p.13 (PDF p.15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Supplement_Grid
import Definitions.Def_AMRangeAvoid_Characterization_SSLB

namespace AMRangeAvoid.Characterization.Supplement

theorem lemma_2_15 (n : ℕ) (hn : 1 ≤ n) (R : ℕ)
    (hR : Real.sqrt n / 2 < (R : ℝ)) (w : Fin n → ℤ)
    (hw : ‖integerEuclidean w‖ ≤ 2 * ((R : ℝ) - Real.sqrt n / 2)) :
    ((gridLens R w).card : ℝ) / (gridBall n R).card ≥
      (1 / Real.sqrt (2 * Real.pi * n)) *
        (((R : ℝ) - Real.sqrt n / 2) / ((R : ℝ) + Real.sqrt n / 2)) ^ n *
        Real.rpow (1 - ‖integerEuclidean w‖ ^ 2 /
          (4 * ((R : ℝ) - Real.sqrt n / 2) ^ 2)) (((n : ℝ) + 1) / 2) := by sorry

end AMRangeAvoid.Characterization.Supplement
