-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_le_two_iff
-- name    : Eden.squaredRadiusEvolution_le_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:30.433062+00:00
-- url     : https://prove2.me/theorems/7b8ee0f2-030a-4439-ad5a-986d9ba8b9fb
-- title:
--   Eden: squared Radius Evolution le two iff
-- statement:
--   The Eden construction uses the squared Radius Evolution le two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L41-L43
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L41-L43

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.squaredRadiusEvolution_le_two_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s ≤ 2 ↔ s ≤ 2 := by sorry
