-- Prove2me | Theorems.Thm_D1Bound5_FrontierTableRow_parameters
-- name    : D1Bound5.FrontierTableRow.parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:57.282639+00:00
-- url     : https://prove2.me/theorems/4894e6f4-b712-43bc-9eb8-bb8bf8a6c308
-- title:
--   Frontier Table Row — parameters
-- statement:
--   All listed parameter rows satisfy the positivity and ordering conditions needed by the determinant estimate.
-- source:
--   D1Bound5/FrontierTableNumeric.lean, lines 13-22, SHA-256 fdb5110fd7c01a02f52f2b7aca40f48eff76285798bc764522ee4ed8858163e4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FrontierScalarReduction_Definitions
import Definitions.Def_D1Bound5_FrontierTableNumeric_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.FrontierTableRow.parameters {alpha beta target : ℝ}
    (h : FrontierTableRow alpha beta target) :
    0 < alpha ∧ 3 ≤ beta ∧ alpha ≤ beta ∧ 5 < alpha*beta ∧
      0 ≤ frontierK alpha beta ∧ 0 ≤ frontierL alpha beta ∧
      0 ≤ frontierQ alpha beta := by sorry



end D1Bound5
end
