-- Prove2me | Theorems.Thm_Eden_tendsto_radialDiscriminant
-- name    : Eden.tendsto_radialDiscriminant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:08.882873+00:00
-- url     : https://prove2.me/theorems/133a5b6a-382c-4e79-8f11-038fd8a696a2
-- title:
--   Eden: tendsto radial Discriminant
-- statement:
--   The Eden construction uses the tendsto radial Discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L113-L118
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L113-L118

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.tendsto_radialDiscriminant (s : ℝ) :
    Tendsto (fun t => radialDiscriminant t s) atTop (𝓝 ((s - 1) ^ 2)) := by sorry
