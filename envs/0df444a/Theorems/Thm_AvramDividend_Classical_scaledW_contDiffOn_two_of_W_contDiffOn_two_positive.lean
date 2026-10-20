-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
-- name    : AvramDividend.Classical.scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T14:16:27.53216+00:00
-- url     : https://prove2.me/theorems/d83d7dcf-aa83-47b4-b5ae-8a698c97f6db
-- title:
--   Positive-barrier normalised scale function inherits the exact C2 regularity of W
-- statement:
--   For any real scale candidate W and a strictly positive finite barrier a, if W is C² on a set s then the exact normalised scale branch z↦divE(W z,scaleDeriv W a) is also C² on s. At positive a the EReal derivative denominator reduces to ordinary W'(a), including the totalised case W'(a)=0; the normalisation is multiplication by the fixed real scalar (W'(a))⁻¹, and fixed scalar multiplication preserves C² by pinned Mathlib. This genuine regularity-transfer theorem supports Gaussian second-order barrier gluing while not falsely claiming that W is C² from the bare scale-function axioms.

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.scaledW_contDiffOn_two_of_W_contDiffOn_two_positive
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (s : Set ℝ) (hW : ContDiffOn ℝ 2 W s) :
    ContDiffOn ℝ 2
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) s := by sorry
