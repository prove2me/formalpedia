-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_lt_two_iff
-- name    : Eden.squaredRadiusEvolution_lt_two_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:42.656723+00:00
-- url     : https://prove2.me/theorems/d44a8b7f-c5e7-570f-991e-27c48e7d1e2d
-- title:
--   Eden: squared Radius Evolution lt two iff
-- statement:
--   The Eden construction uses the squared Radius Evolution lt two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L45-L47
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L45-L47

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.squaredRadiusEvolution_lt_two_iff {t s : ℝ} (ht : 0 ≤ t) :
    squaredRadiusEvolution t s < 2 ↔ s < 2 := by sorry
