-- Prove2me | Theorems.Thm_Erdos266_shifted_sum_rational
-- name    : Erdos266.shifted_sum_rational
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:37:42.098207+00:00
-- url     : https://prove2.me/theorems/9cd4c431-a81f-5e90-bd7b-74e7befc8445
-- title:
--   Erdos266: shifted sum rational
-- statement:
--   The heart of the reduction: by strong induction on the shift index,
--   every series `∑ₙ (aₙ + tⱼ)⁻¹` has a rational sum.
--
--   (No independent summability hypothesis is needed: the `HasSum` hypotheses on
--   the `f`-series carry all the required convergence through the induction —
--   a simplification over the paper's presentation surfaced by formalizing.)
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L110-L187
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L110-L187

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}

theorem Erdos266.shifted_sum_rational (ha : StrictMono a)
    (hf : ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    ∀ j : ℕ, ∃ q : ℚ, HasSum (fun n => ((a n : ℝ) + (tSeq j : ℝ))⁻¹) (q : ℝ) := by sorry
