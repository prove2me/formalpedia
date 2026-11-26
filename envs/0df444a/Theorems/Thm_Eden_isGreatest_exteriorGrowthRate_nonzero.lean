-- Prove2me | Theorems.Thm_Eden_isGreatest_exteriorGrowthRate_nonzero
-- name    : Eden.isGreatest_exteriorGrowthRate_nonzero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:42:31.031745+00:00
-- url     : https://prove2.me/theorems/408a326f-6492-542e-aced-8ac5a1a253b2
-- title:
--   Eden: is Greatest exterior Growth Rate nonzero
-- statement:
--   The Eden construction uses the is Greatest exterior Growth Rate nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L123-L132
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L123-L132

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

theorem Eden.isGreatest_exteriorGrowthRate_nonzero {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (exteriorGrowthRate k c p '' {v : ExteriorSpace k | v ≠ 0})
      (spectrumPartialSum (lyapunovExponent c p) k) := by sorry
