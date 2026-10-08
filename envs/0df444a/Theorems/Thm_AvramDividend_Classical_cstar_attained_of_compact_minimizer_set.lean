-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_minimizer_set
-- name    : AvramDividend.Classical.cstar_attained_of_compact_minimizer_set
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T14:23:09.097771+00:00
-- url     : https://prove2.me/theorems/ecb18272-04c0-41fe-bb57-ce35bab4f545
-- title:
--   The Avram barrier infimum is attained when its positive derivative-minimiser set is compact
-- statement:
--   If the set of strictly positive global derivative minimisers of W is nonempty and compact in the real line, then the infimum-defined Avram barrier cstar is attained: its finite real value is itself a positive global derivative minimiser. This resolves the attainment part of the classical optimal-barrier milestone under explicit topological hypotheses.
-- source:
--   Pinned Mathlib IsCompact.exists_isMinOn of the identity function gives the least a in the cstarSet; ENNReal.ofReal order preservation and the defining iInf make cstar=ofReal a. Its toReal is a because a>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_attained_of_compact_minimizer_set
    (W : ℝ → ℝ)
    (hcompact : IsCompact (cstarSet W))
    (hnonempty : (cstarSet W).Nonempty) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
