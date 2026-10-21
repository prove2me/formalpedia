-- Prove2me | Theorems.Thm_DataMerger_Quality_exclusivity
-- name    : DataMerger.Quality.exclusivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:07.550982+00:00
-- url     : https://prove2.me/theorems/c683657a-3c08-4339-9d82-793b8b727eea
-- title:
--   Section 4.3, p. 8 — positive data are sold exclusively
-- statement:
--   In the product-improvement model, suppose the standing conditions hold and the data set has size $\delta>0$. The price of one exclusive licence exceeds the total price of two nonexclusive licences:
--
--   $$T^1(\delta)>2T^2(\delta).$$
--
--   Consequently exclusive supply is selected both when A is independent and after the merger with B1.
--
--   **Formalization Note** At $\delta=0$ the two sides are equal, so the strict claim is for positive data. Strict $V'>0$ is added to the paper's non-decreasing assumption, with coverage and activity bounds included in the standing conditions.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 8 (PDF 9), Section 4.3, opening paragraph

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem exclusivity (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (δ : ℝ) (hδ : 0 < δ) :
    ExclusiveI (piB V) δ ∧ ExclusiveM (piB V) δ := by sorry

end DataMerger.Quality
