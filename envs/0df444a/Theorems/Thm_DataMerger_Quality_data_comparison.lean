-- Prove2me | Theorems.Thm_DataMerger_Quality_data_comparison
-- name    : DataMerger.Quality.data_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:04.647611+00:00
-- url     : https://prove2.me/theorems/41b9a7ca-25b2-43b2-9e8b-18907e3329a9
-- title:
--   Section 4.3, p. 9 — merger reduces equilibrium data collection
-- statement:
--   Let $d_I$ maximize $(\alpha-d)d+\pi_B(d,0)-\pi_B(0,d)$ over nonnegative data quantities, and let $d_M$ maximize $(\alpha-d)d+\pi_B(d,0)$ over the same domain. Under the standing conditions,
--
--   $$0<d_M<d_I,\qquad \alpha-d_I<\alpha-d_M.$$
--
--   This compares the data collected at the two first-stage optimum problems in equations (3) and (4); the price comparison in Proposition 2 follows from the inverse demand relation $p_A(d)=\alpha-d$.
--
--   **Formalization Note** The theorem quantifies over every maximizer. It adds strict $V'>0$ to the paper's non-decreasing assumption and makes coverage and active-firm bounds explicit. Footnote 11's concavity condition is omitted because this comparison holds without it.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 9 (PDF 10), Section 4.3, equations (3)–(4) and paragraph after Proposition 2

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem data_comparison (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (dI dM : ℝ) (hdI : 0 ≤ dI) (hdM : 0 ≤ dM)
    (hI : ∀ d, 0 ≤ d →
      (alpha - d) * d + piB V d 0 - piB V 0 d ≤
        (alpha - dI) * dI + piB V dI 0 - piB V 0 dI)
    (hM : ∀ d, 0 ≤ d →
      (alpha - d) * d + piB V d 0 ≤
        (alpha - dM) * dM + piB V dM 0) :
    0 < dM ∧ dM < dI ∧ alpha - dI < alpha - dM := by sorry

end DataMerger.Quality
