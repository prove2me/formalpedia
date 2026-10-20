-- Prove2me | Theorems.Thm_DerivativeChainPrivate_rb5_thresholds
-- name    : DerivativeChainPrivate.rb5_thresholds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T01:56:29.880985+00:00
-- url     : https://prove2.me/theorems/798e04ab-7781-453a-8925-91c95e6d64d0
-- title:
--   Exact large-degree scalar cutoffs for the two-, three-, and four-pair bounds
-- statement:
--   For c>=0, the scalar RB5 expression is strictly less than 3 when N>=10 and c<=4, strictly less than 7/2 when N>=13 and c<=6, and strictly less than 4 when N>=17 and c<=8. N corresponds to n-1 in the source. This does not assert that any polynomial satisfies the RB5 estimate.
-- source:
--   Derivative-zero chains: public formalization reference, R35, DerivativeChainPrivate.rb5_thresholds. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace DerivativeChainPrivate
end DerivativeChainPrivate

theorem DerivativeChainPrivate.rb5_thresholds (N c : ℝ) (hc : 0 ≤ c) :
    (10 ≤ N → c ≤ 4 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < 3) ∧
    (13 ≤ N → c ≤ 6 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < (7 : ℝ) / 2) ∧
    (17 ≤ N → c ≤ 8 → 1 + Real.sqrt (1 + c ^ 2 / (N - c)) < 4) := by sorry
