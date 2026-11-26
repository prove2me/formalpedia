-- Prove2me | Theorems.Thm_Eden_equilibriumSet_eq_singleton
-- name    : Eden.equilibriumSet_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:14:17.992944+00:00
-- url     : https://prove2.me/theorems/6632656b-0ac1-5362-abc1-b273b09c0771
-- title:
--   Eden: equilibrium Set eq singleton
-- statement:
--   The Eden construction uses the equilibrium Set eq singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L76-L79
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean#L76-L79

import Definitions.Def_Eden_RotationReturns
import Definitions.Def_Eden_PeriodicSets
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.equilibriumSet_eq_singleton {c : ℝ} (hc : c ≠ 0) :
    equilibriumSet c = {0} := by sorry
