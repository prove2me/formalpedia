-- Prove2me | Theorems.Thm_Eden_isGreatest_exteriorRate
-- name    : Eden.isGreatest_exteriorRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:20.787637+00:00
-- url     : https://prove2.me/theorems/45cb990c-dd5f-5da0-9693-83be9a47a0c5
-- title:
--   Eden: is Greatest exterior Rate
-- statement:
--   The Eden construction uses the is Greatest exterior Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L96-L107
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L96-L107

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

theorem Eden.isGreatest_exteriorRate {k : ℕ} (hk : k ≤ 5) (c : ℝ) (p : PhaseSpace) :
    IsGreatest (Set.range (exteriorRate k c p)) (spectrumPartialSum (lyapunovExponent c p) k) := by sorry
