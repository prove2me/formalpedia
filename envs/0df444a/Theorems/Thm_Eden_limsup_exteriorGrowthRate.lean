-- Prove2me | Theorems.Thm_Eden_limsup_exteriorGrowthRate
-- name    : Eden.limsup_exteriorGrowthRate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:42:02.771243+00:00
-- url     : https://prove2.me/theorems/d87a28fd-d668-52bf-a39f-b9255ebbc9e8
-- title:
--   Eden: limsup exterior Growth Rate
-- statement:
--   The Eden construction uses the limsup exterior Growth Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L38-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L38-L42

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

theorem Eden.limsup_exteriorGrowthRate {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    limsup (fun t => Real.log ‖exteriorEvolution k c t p v‖ / t) atTop =
      exteriorGrowthRate k c p v := by sorry
