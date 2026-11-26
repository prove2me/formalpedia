-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_isGreatest
-- name    : Eden.finiteTimeDimension_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:23.057085+00:00
-- url     : https://prove2.me/theorems/92563664-084e-5505-a368-8a24b2dd4c7b
-- title:
--   Eden: finite Time Dimension is Greatest
-- statement:
--   The Eden construction uses the finite Time Dimension is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L146-L149
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L146-L149

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_isGreatest (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    IsGreatest (admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap)
      (finiteTimeDimension c t p) := by sorry
