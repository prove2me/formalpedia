-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_analytic_conductor
-- name    : Formalism.ZeroFreeDirichlet.log_two_le_log_analytic_conductor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:35.003602+00:00
-- url     : https://prove2.me/theorems/982ba5a2-49cf-4791-9151-c53d3923c1b2
-- title:
--   Zero Free Dirichlet: log two le log analytic conductor
-- statement:
--   The Zero Free Dirichlet construction uses the log two le log analytic conductor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LogTwoLeLogAnalyticConductor.lean#L12-L15

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.log_two_le_log_analytic_conductor (q : ℕ) [NeZero q] (t : ℝ) : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by sorry
