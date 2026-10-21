-- Prove2me | Theorems.Thm_DataMerger_Quality_lemma_2_ii
-- name    : DataMerger.Quality.lemma_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:45.071515+00:00
-- url     : https://prove2.me/theorems/1f43347f-bee7-4b11-8591-0096a35d8da6
-- title:
--   Lemma 2 (ii), p. 7 — rival data strictly lowers B-firm profit
-- statement:
--   In the product-improvement model, let $d,d'\ge0$ be the data quantities held by a B firm and its rival. Under the standing conditions, the firm's equilibrium profit decreases strictly as its rival gets more data:
--
--   $$\frac{\partial\pi_B(d,d')}{\partial d'}<0.$$
--
--   This captures the competitive effect of improving the rival's quality and enters the comparison of independent and merged incentives to collect data.
--
--   **Formalization Note** Strictly positive $V'$ is added to the paper's non-decreasing assumption; covered-market and active-firm bounds are explicit in the standing conditions.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 7 (PDF 8), Lemma 2 (ii)

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem lemma_2_ii (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d d' : ℝ) (hd : 0 ≤ d) (hd' : 0 ≤ d') :
    deriv (fun x => piB V d x) d' < 0 := by sorry

end DataMerger.Quality
