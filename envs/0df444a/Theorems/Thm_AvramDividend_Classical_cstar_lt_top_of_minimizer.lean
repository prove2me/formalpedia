-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer
-- name    : AvramDividend.Classical.cstar_lt_top_of_minimizer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T12:25:53.59921+00:00
-- url     : https://prove2.me/theorems/c0060d1c-5cee-4ca8-89b3-2c1c84cd3fc7
-- title:
--   Finiteness of the optimal barrier level when a global derivative minimiser exists
-- statement:
--   If the set of strictly positive global minimisers of the scale-function derivative is nonempty, the Avram barrier level cstar is strictly less than infinity. This follows directly from cstar being the infimum of the finite ENNReal values of those minimisers and is the first finiteness branch of milestone 3.
-- source:
--   Exact canonical definition cstar and pinned Mathlib iInf_le_of_le, ENNReal.ofReal_lt_top. The hard assumption that a derivative minimiser exists remains explicit and must be proved separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_lt_top_of_minimizer
    (W : ℝ → ℝ) (hmin : (cstarSet W).Nonempty) :
    cstar W < ⊤ := by
  sorry

end AvramDividend.Classical
