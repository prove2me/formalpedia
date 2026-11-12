-- Prove2me | Theorems.Thm_BunkbedAux_wt_refine
-- name    : BunkbedAux.wt_refine
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T01:03:08.403352+00:00
-- url     : https://prove2.me/theorems/50263126-b9a4-432f-a5f2-2c9e0ce274cc
-- title:
--   The refinement of the pair state space changes no probability
-- statement:
--   The refinement of the Wierman--Ziff pair state space splits each of the two pairs $(abc,\,a|b|c)$ and $(a|b|c,\,abc)$ into a $+$ and a $-$ variant, with weights
--   $$\mathbb{P}\bigl[(abc,a|b|c)^{+}\bigr] = P_{ab|c}P_{ac|b}, \qquad \mathbb{P}\bigl[(abc,a|b|c)^{-}\bigr] = P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}.$$
--
--   This theorem records that the refinement is *measure-preserving*: for each split pair the two variant weights sum to the weight $P_{abc}P_{a|b|c}$ of the unsplit pair,
--   $$P_{ab|c}P_{ac|b} + \bigl(P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}\bigr) = P_{abc}P_{a|b|c},$$
--   and likewise for the mirror pair. Consequently no probability computed in the refined model differs from the corresponding probability in the original model — the refinement is pure bookkeeping, introduced solely to give the half-reflection involution a domain on which to act.
--
--   It also records the two basic properties of the reflection involution $\rho$, which exchanges the two levels: it transposes the underlying pair of states, and it preserves weights, the latter because a configuration's weight is symmetric under swapping the two levels.
--
--   **Mathematical role.** Together these are what license passing back and forth between the original and the refined model. The second point is why the involution used in the robustness lemma can apply $\rho$ freely to all hyperedges beyond a chosen one without disturbing any weight, and the first is why the resulting cancellation is a statement about the original Wierman--Ziff probabilities rather than about an auxiliary measure.
--
--   Note that the quantity $P_{abc}P_{a|b|c} - P_{ab|c}P_{ac|b}$ appearing as the weight of the $-$ variants is exactly the determinant-like expression of Eq. [1] of the source, whose positivity drives the whole argument.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 3.3, Eq. [4] (p. 4), and Definition 3.5 (p. 4).

import Definitions.Def_BunkbedWZRefined
open Bunkbed.Hyper

namespace BunkbedAux

/-- **The refinement changes no probability.** The `+` and `-` variants of each split pair have
weights summing to the weight of the unsplit pair, and the level swap `rho` transposes the
underlying pair while preserving weights. -/
theorem wt_refine (P : WZ → ℚ) :
    WZExt.wt P (Sum.inr 0) + WZExt.wt P (Sum.inr 1) = P WZ.abc * P WZ.a_b_c ∧
    WZExt.wt P (Sum.inr 2) + WZExt.wt P (Sum.inr 3) = P WZ.a_b_c * P WZ.abc ∧
    (∀ q : WZExt, WZExt.toPair (WZExt.rho q)
      = ((WZExt.toPair q).2, (WZExt.toPair q).1)) ∧
    (∀ q : WZExt, WZExt.wt P (WZExt.rho q) = WZExt.wt P q) := by
  sorry

end BunkbedAux
