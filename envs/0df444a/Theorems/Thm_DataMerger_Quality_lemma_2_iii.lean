-- Prove2me | Theorems.Thm_DataMerger_Quality_lemma_2_iii
-- name    : DataMerger.Quality.lemma_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:54.883304+00:00
-- url     : https://prove2.me/theorems/2f482d2f-89a8-46cc-bfd8-11bf33652448
-- title:
--   Lemma 2 (iii), pp. 7–8 — either firm's data raises B-market consumer surplus
-- statement:
--   Let $U_B(d_1,d_2)$ be total consumer surplus on the covered Hotelling segment at the equilibrium B prices, when firms B1 and B2 hold nonnegative data quantities $d_1$ and $d_2$. Under the standing conditions, surplus rises strictly with either firm's data:
--
--   $$\frac{\partial U_B(d_1,d_2)}{\partial d_1}>0,\qquad \frac{\partial U_B(d_1,d_2)}{\partial d_2}>0.$$
--
--   This connects data allocation and collection to consumer welfare in the B market.
--
--   **Formalization Note** $U_B$ is the paper's two-part integral, with transportation cost one. Strict $V'>0$ is added to the paper's non-decreasing assumption; the standing conditions make coverage and both firms' activity explicit. The paper's index slip in the proof is not used.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), pp. 7–8 (PDF 8–9), Lemma 2 (iii) and proof

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem lemma_2_iii (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (d1 d2 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) :
    0 < deriv (fun x => UB V x d2) d1 ∧
      0 < deriv (fun x => UB V d1 x) d2 := by sorry

end DataMerger.Quality
