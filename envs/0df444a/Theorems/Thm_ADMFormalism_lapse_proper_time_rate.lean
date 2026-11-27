-- Prove2me | Theorems.Thm_ADMFormalism_lapse_proper_time_rate
-- name    : ADMFormalism.lapse_proper_time_rate
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T03:06:28.130801+00:00
-- url     : https://prove2.me/theorems/30e4528d-8a10-58a6-8bbc-adb8ab26b5e8
-- title:
--   The lapse encodes the proper-time rate of the normal observers
-- statement:
--   The lapse encodes the proper-time rate of the normal observers.  Formally: the observer whose tangent at (t, x) is (1, -N^i) (coordinate time one, no spatial drift) has sqrt(-(admForm D t x u u)) = N t x, i.e. dtau = N dt - the source's 'N is the lapse function encoding the proper time evolution'.
-- source:
--   Wikipedia, ADM formalism, https://en.wikipedia.org/wiki/ADM_formalism (source of the quoted statements, reproduced verbatim in the definition file) ('N is the lapse function encoding the proper time evolution')

import Mathlib
import Definitions.Def_ADMFormalism

namespace ADMFormalism

/-! The proper-time rate of the normal observers is the lapse: the observer
with tangent `(1, -N^i)` (coordinate time one, no spatial drift) has
`dτ = N dt`, "the lapse function encoding the proper time evolution". -/

theorem lapse_proper_time_rate (D : ADMFormalism.ADMData) (t : ℝ) (x : ADMFormalism.Spc3) :
    Real.sqrt (-(ADMFormalism.admForm D t x (1, fun i => -(D.ns t x i))
      (1, fun i => -(D.ns t x i)))) = D.N t x := by
  sorry

end ADMFormalism
