-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary
-- name    : AvramDividend.Classical.cstar_lt_top_iff_minimizer_or_zero_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T13:12:24.098339+00:00
-- url     : https://prove2.me/theorems/b45e8106-4138-43ad-939f-b14a3ae235ec
-- title:
--   Exact characterisation of finite Avram barrier level by derivative minimisers or the zero-boundary condition
-- statement:
--   For an arbitrary real-valued candidate scale function, the canonical Avram barrier level cstar is finite if and only if either there is a strictly positive global minimiser of its derivative or the extended right derivative at zero is a lower bound for every positive derivative. This exposes the exact mathematical dichotomy that must be established to finish the canonical cstar finiteness milestone, with no extra regularity assumptions.
-- source:
--   Expand exact cstar definition. In the positive-minimiser branch, use the separately authored finite-from-minimiser lemma. If that set is empty, cstar is 0 exactly when the zero-boundary derivative lower-bound condition holds and top otherwise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_lt_top_iff_minimizer_or_zero_boundary (W : ℝ → ℝ) :
    cstar W < ⊤ ↔
      (cstarSet W).Nonempty ∨
        ∀ x : ℝ, 0 < x →
          derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
  sorry

end AvramDividend.Classical
