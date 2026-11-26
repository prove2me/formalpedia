-- Prove2me | Theorems.Thm_Erdos266_slope_lemma
-- name    : Erdos266.slope_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:11.534218+00:00
-- url     : https://prove2.me/theorems/65e18871-bfb6-5458-a19b-95e3048f8a80
-- title:
--   Erdos266: slope lemma
-- statement:
--   **Lemma 7.1 of [KoTa24]** with an existential constant: near a large
--   `N`, the function `fᵢ` is locally linear with slope `-i/N^(i+1)`, with a
--   quadratic error.  The hypothesis is the paper's `|n| ≤ N/4i`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L153-L419
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L153-L419

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
set_option maxHeartbeats 1600000

theorem Erdos266.slope_lemma (i : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (n : ℤ),
      4 * (i : ℝ) * |(n : ℝ)| ≤ (N : ℝ) →
      |f i (N : ℝ) - f i ((N : ℝ) + (n : ℝ)) - i * n / (N : ℝ) ^ (i + 1)|
        ≤ C * (n : ℝ) ^ 2 / (N : ℝ) ^ (i + 2) := by sorry
