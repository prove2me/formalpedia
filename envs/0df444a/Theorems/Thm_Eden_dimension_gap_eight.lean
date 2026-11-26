-- Prove2me | Theorems.Thm_Eden_dimension_gap_eight
-- name    : Eden.dimension_gap_eight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:23:32.945152+00:00
-- url     : https://prove2.me/theorems/149e2301-e95c-5183-aac1-48ecba4d157b
-- title:
--   Eden: dimension gap eight
-- statement:
--   The exact specialization c=8, retaining attainment of both periodic maxima and
--   the separately defined global Lyapunov dimension.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L65-L71
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGap.lean#L65-L71

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.dimension_gap_eight {t : ℝ} (ht : 0 < t) :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
      IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3 := by sorry
