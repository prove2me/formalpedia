-- Prove2me | Theorems.Thm_Eden_two_lt_squaredRadiusEvolution_iff
-- name    : Eden.two_lt_squaredRadiusEvolution_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:47.164856+00:00
-- url     : https://prove2.me/theorems/99f212ac-b728-5f9e-be41-e436ffdcf513
-- title:
--   Eden: two lt squared Radius Evolution iff
-- statement:
--   The Eden construction uses the two lt squared Radius Evolution iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L49-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L49-L51

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.two_lt_squaredRadiusEvolution_iff {t s : ℝ} (ht : 0 ≤ t) :
    2 < squaredRadiusEvolution t s ↔ 2 < s := by sorry
