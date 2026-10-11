-- Prove2me | Theorems.Thm_ActuarialFoundations_fa_R_absolute_conversion
-- name    : ActuarialFoundations.fa_R_absolute_conversion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T23:34:46.958312+00:00
-- url     : https://prove2.me/theorems/64bdbf20-a946-4758-b16f-841522f931a2
-- title:
--   R absolute conversion
-- statement:
--   Prove conversion from relative-duration to absolute-age increasing-benefit conventions for the stated exact Lean assumptions, directly from the life-table and cashflow definitions. The claim is valued at the end of the death year, and terminal-age endpoints are disjoint. No commutation equivalence or desired result may be inserted as a hypothesis.
-- source:
--   Institute of Actuaries (1971), International Actuarial Notation, commutation functions, p.50, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf. Original derived theorem; not a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_faM
import Definitions.Def_actuarial_faR
import Definitions.Def_actuarial_faRAbsolute

namespace ActuarialFoundations

theorem fa_R_absolute_conversion (l : ℕ → ℝ) (v : ℝ) (ω x : ℕ) : faRAbsolute l v ω x = faR l v ω x + (x : ℝ) * faM l v ω x := by sorry

end ActuarialFoundations
