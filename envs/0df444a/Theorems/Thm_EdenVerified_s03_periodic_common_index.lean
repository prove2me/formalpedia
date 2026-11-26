-- Prove2me | Theorems.Thm_EdenVerified_s03_periodic_common_index
-- name    : EdenVerified.s03_periodic_common_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:21:48.73064+00:00
-- url     : https://prove2.me/theorems/f0c78172-9313-5621-b79f-a9e415642e93
-- title:
--   Eden Verified: s03 periodic common index
-- statement:
--   The global index remains fixed when maximisation is restricted to periodic
--   points.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L184-L191
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L184-L191

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s03_periodic_common_index (c : ℝ) (hc : 4 < c) :
    IsGreatest (commonIndexLocalDimension c '' periodicEquilibriumSet c) (4-2/c) ∧
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) < commonIndexDimension c ∧
    IsGreatest (asymptoticDimension c '' periodicEquilibriumSet c) 3 ∧
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) := by sorry
