-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_welfare_loss
-- name    : DynDoubleAuction.TwoSided.welfare_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:44.242774+00:00
-- url     : https://prove2.me/theorems/618f5685-830c-428c-8fd5-eae8e53dc29b
-- title:
--   Proof of Theorem 5.3 — welfare loss after first exit
-- statement:
--   Let $\tau$ be the first period at which the seller's promise enters either inefficient region, with $\tau=T+1$ if no exit occurs before the horizon. For a common initial promise $w^1\in[0,\mu T]$, the mechanism's expected welfare $S$ satisfies
--
--   $$\Pi^{\mathrm{FB}}-S\le\bar v\,\mathbb E[(T-\tau+1)^+].$$
--
--   The bound charges at most one value range $\bar v$ for each period from the first exit through the horizon. It is the welfare-loss display in the proof of Theorem 5.3.
--
--   **Formalization Note** The stopping time is clipped at $T+1$, so the loss count is zero if there is no exit.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), p. 29, proof of Theorem 5.3

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- In the proof of Theorem 5.3, every period after first exit loses at most `vbar`. -/
theorem welfare_loss {n : ℕ} (M : Market n) (hM : Standing M)
    (T : ℕ) (w1 : ℝ) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1) :
    firstBest M T - expectedWelfare M T w1 ≤
      M.vbar *
        (∫ vs, max ((T : ℝ) - (exitTime M T w1 vs : ℝ) + 1) 0 ∂valueLaw M) := by sorry
end DynDoubleAuction.TwoSided
