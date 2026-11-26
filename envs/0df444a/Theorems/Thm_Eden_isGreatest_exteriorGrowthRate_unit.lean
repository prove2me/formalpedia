-- Prove2me | Theorems.Thm_Eden_isGreatest_exteriorGrowthRate_unit
-- name    : Eden.isGreatest_exteriorGrowthRate_unit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:42:28.583059+00:00
-- url     : https://prove2.me/theorems/c3cab768-ff94-4d65-8d23-148dcc241de5
-- title:
--   Eden: is Greatest exterior Growth Rate unit
-- statement:
--   The largest growth rate over unit k-vectors is precisely the sum of
--   the first k ordered Lyapunov exponents, and is attained.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L111-L121
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L111-L121

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.isGreatest_exteriorGrowthRate_unit {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | ‖v‖ = 1})
      (spectrumPartialSum (lyapunovExponent c p) k) := by sorry
