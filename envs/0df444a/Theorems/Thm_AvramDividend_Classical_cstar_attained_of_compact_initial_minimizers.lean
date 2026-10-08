-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers
-- name    : AvramDividend.Classical.cstar_attained_of_compact_initial_minimizers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:32:25.723986+00:00
-- url     : https://prove2.me/theorems/a38e853f-a28a-41ee-a5d7-b1fe16f6beaf
-- title:
--   Attainment of the infimum-defined Avram barrier from compact minimisers below one known minimiser
-- statement:
--   Given any positive global minimiser a of the scale-function derivative, it is enough for the subset of such minimisers in the bounded interval [0,a] to be compact. Then the least point in that compact subset is also the least global positive derivative minimiser, and its value equals cstar. Unlike a theorem requiring all positive minimisers to form a compact set, this allows unbounded sets of minimisers to the right.
-- source:
--   Pinned Mathlib IsCompact.exists_isLeast on cstarSet W intersect Icc 0 a gives a least b in this compact initial section. Any global minimiser c either lies below a and obeys minimality of b or lies above a and thus above b. Using order preservation of ENNReal.ofReal identifies the iterated iInf defining cstar with ofReal b; toReal b is b>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_attained_of_compact_initial_minimizers
    (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a)) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
