-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_lemma_7
-- name    : AdaptiveStepIPM.Probabilistic.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:19.595522+00:00
-- url     : https://prove2.me/theorems/e911cd14-7621-4125-bf45-58165ca2a1b9
-- title:
--   Lemma 7 — sup norm of a uniform spherical direction
-- statement:
--   For every $n\ge2$, let $F_n=[g_n,H_n]$ be an orthogonal matrix, and draw $v_n$ uniformly from the unit sphere in $\mathbb R^{n-1}$. The frames may vary arbitrarily with $n$. Then
--
--   $$
--   \Pr\!\left(\|H_nv_n\|_\infty
--     \le\sqrt{\frac{3\log n}{n}}\right)
--     \longrightarrow1\quad\text{as }n\longrightarrow\infty.
--   $$
--
--   This is the probabilistic coordinate bound applied to the direction from Lemma 6 in the proof of Theorem 5.
--
--   **Formalization Note** The spherical law is the normalized standard Gaussian law. The finitely many dimensions below two are assigned probability one in the limit expression; no orthogonal frame is requested there.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 15, Lemma 7; https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Lemma 7 for an arbitrary sequence of orthogonal frames. -/
theorem lemma_7 (F : ∀ n : ℕ, 2 ≤ n → Frame n) :
    Tendsto (fun n : ℕ =>
      if hn : 2 ≤ n then
        ((sphereGaussian (n - 1))
          {v | supNorm ((F n hn).H v) ≤
            Real.sqrt (3 * Real.log (n : ℝ) / (n : ℝ))}).toReal
      else 1) atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic
