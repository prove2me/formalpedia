-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_pos_iff
-- name    : Eden.squaredRadiusEvolution_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:30.375785+00:00
-- url     : https://prove2.me/theorems/d3e57018-1c40-5fa6-b9f7-fa421171621b
-- title:
--   Eden: squared Radius Evolution pos iff
-- statement:
--   The Eden construction uses the squared Radius Evolution pos iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L29-L31
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L29-L31

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.squaredRadiusEvolution_pos_iff {t s : ℝ} (ht : 0 ≤ t) :
    0 < squaredRadiusEvolution t s ↔ 0 < s := by sorry
