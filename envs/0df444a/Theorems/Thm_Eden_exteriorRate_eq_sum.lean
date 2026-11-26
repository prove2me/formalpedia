-- Prove2me | Theorems.Thm_Eden_exteriorRate_eq_sum
-- name    : Eden.exteriorRate_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:03.24216+00:00
-- url     : https://prove2.me/theorems/36a4b5d2-3e94-5c0c-bab1-5eb16c4b1f99
-- title:
--   Eden: exterior Rate eq sum
-- statement:
--   The Eden construction uses the exterior Rate eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L81-L86
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorMaximalGrowth.lean#L81-L86

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

theorem Eden.exteriorRate_eq_sum (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorRate k c p s = ∑ j ∈ s.val, factorExponents c p j := by sorry
