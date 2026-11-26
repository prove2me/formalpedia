-- Prove2me | Theorems.Thm_Eden_exteriorGrowthRate_eq
-- name    : Eden.exteriorGrowthRate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:08.837491+00:00
-- url     : https://prove2.me/theorems/3a89b734-5da5-540b-8aa1-00917e016002
-- title:
--   Eden: exterior Growth Rate eq
-- statement:
--   The Eden construction uses the exterior Growth Rate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L25-L29
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L25-L29

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

theorem Eden.exteriorGrowthRate_eq {k : ℕ} (c : ℝ) (p : PhaseSpace)
    {v : ExteriorSpace k} (hv : v ≠ 0) :
    exteriorGrowthRate k c p v =
      (exteriorSupport k p v).sup' (exteriorSupport_nonempty p hv) (exteriorRate k c p) := by sorry
