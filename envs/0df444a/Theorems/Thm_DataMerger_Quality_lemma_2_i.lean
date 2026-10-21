-- Prove2me | Theorems.Thm_DataMerger_Quality_lemma_2_i
-- name    : DataMerger.Quality.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:45.80415+00:00
-- url     : https://prove2.me/theorems/1878e2a4-f265-4c3a-af42-e47fbe9a234d
-- title:
--   Lemma 2 (i), p. 7 — own data strictly raises B-firm profit
-- statement:
--   In the product-improvement model, let $d,d'\ge0$ be the data quantities held by a B firm and its rival. If the standing conditions hold, the firm's equilibrium profit increases strictly with its own data:
--
--   $$\frac{\partial\pi_B(d,d')}{\partial d}>0.$$
--
--   This is the own-data comparative static used in the paper's merger analysis.
--
--   **Formalization Note** The paper assumes $V$ is non-decreasing but states a strict inequality. The standing conditions add $V'(d)>0$ for nonnegative data and make explicit the covered-market and active-firm bounds.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 7 (PDF 8), Lemma 2 (i)

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem lemma_2_i (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d d' : ℝ) (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    0 < deriv (fun x => piB V x d') d := by sorry

end DataMerger.Quality
