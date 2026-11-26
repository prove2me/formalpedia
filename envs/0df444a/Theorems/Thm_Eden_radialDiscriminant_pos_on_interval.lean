-- Prove2me | Theorems.Thm_Eden_radialDiscriminant_pos_on_interval
-- name    : Eden.radialDiscriminant_pos_on_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:03:32.731335+00:00
-- url     : https://prove2.me/theorems/ac0d564f-13a1-5fef-9d92-b3689b7a8f03
-- title:
--   Eden: radial Discriminant pos on interval
-- statement:
--   Inside the closed radial interval the formula is defined for all real time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L77-L86
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialDynamics.lean#L77-L86

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden

theorem Eden.radialDiscriminant_pos_on_interval (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : 0 < radialDiscriminant t s := by sorry
