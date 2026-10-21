-- Prove2me | Theorems.Thm_DataMerger_Quality_proposition_2
-- name    : DataMerger.Quality.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:25.783962+00:00
-- url     : https://prove2.me/theorems/1ea872ca-b816-4b8a-8362-75d6fde969bb
-- title:
--   Proposition 2, p. 9 — data trade makes the merger raise prices and lower consumer surplus
-- statement:
--   In the product-improvement model with data trade, let $p_A^I$ and $p_A^M$ be any maximizing first-stage prices of independent A and merged A–B1. Each objective includes the choice between exclusive and nonexclusive data supply. At the resulting data allocations, compare the data holder with the data holder and its rival with its rival. Then
--
--   $$p_A^I<p_A^M,\qquad \widetilde p_{B,j}^I<\widetilde p_{B,j}^M\quad(j=1,2),\qquad CS_A^M<CS_A^I,\qquad U_B^M<U_B^I,$$
--
--   where $\widetilde p_{B,j}=p_{B,j}-V(d_j)$ is the quality-adjusted price and $CS_A,U_B$ are consumer surplus in the two markets. Thus the merger raises A's price and both quality-adjusted B prices while reducing consumer surplus on both markets.
--
--   **Formalization Note** The independent exclusive buyer is labelled first; after the merger that holder is B1. Prices of A range over all $\mathbb R$. The standing conditions add $V'(d)>0$ for $d\ge0$ to obtain the paper's strict comparisons, and spell out coverage and both B firms' activity. The theorem addresses every maximizer, and footnote 11's concavity condition is omitted. Existence of maximizers follows from the objective's continuity and behavior at the price extremes but is not asserted here.
-- source:
--   de Cornière & Taylor, Data-Driven Mergers, TSE Working Paper No. 1576 (Sept. 2024; manuscript of Dec. 20, 2023), p. 9 (PDF 10), Proposition 2

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

namespace DataMerger.Quality

theorem proposition_2 (alpha : ℝ) (V : ℝ → ℝ) (hS : Standing alpha V)
    (pI pM : ℝ) (hI : ∀ p, objI alpha V p ≤ objI alpha V pI)
    (hM : ∀ p, objM alpha V p ≤ objM alpha V pM) :
    let aI := allocI (piB V) (DA alpha pI)
    let aM := allocM (piB V) (DA alpha pM)
    pI < pM ∧
      qaPrice V aI.1 aI.2 < qaPrice V aM.1 aM.2 ∧
      qaPrice V aI.2 aI.1 < qaPrice V aM.2 aM.1 ∧
      CSA alpha pM < CSA alpha pI ∧
      UB V aM.1 aM.2 < UB V aI.1 aI.2 := by sorry

end DataMerger.Quality
