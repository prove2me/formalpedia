-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_powerDense
-- name    : FirstPassageLinearTransport.bootstrapSet_powerDense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:51.7327+00:00
-- url     : https://prove2.me/theorems/558baffe-1d4f-43d2-8012-ea1853ae7408
-- title:
--   First Passage Linear Transport: bootstrap Set power Dense
-- statement:
--   Iterated density theorem.  The only analytic input is the already
--   compiled one-stage first-passage pullback theorem.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L103-L124
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L103-L124

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.bootstrapSet_powerDense
    {r eta chi Dc : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1) :
    ∀ R, PowerDense (bootstrapSet p R)
      (bootstrapC p chi Dc R) (bootstrapD chi Dc R) := by sorry
