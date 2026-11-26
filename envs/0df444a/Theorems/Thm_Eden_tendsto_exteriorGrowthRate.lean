-- Prove2me | Theorems.Thm_Eden_tendsto_exteriorGrowthRate
-- name    : Eden.tendsto_exteriorGrowthRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:41.221682+00:00
-- url     : https://prove2.me/theorems/2366db22-22cb-4824-accd-55dc9d169378
-- title:
--   Eden: tendsto exterior Growth Rate
-- statement:
--   The Eden construction uses the tendsto exterior Growth Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L31-L36
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L31-L36

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

theorem Eden.tendsto_exteriorGrowthRate {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    Tendsto (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop
      (𝓝 (exteriorGrowthRate k c p v)) := by sorry
