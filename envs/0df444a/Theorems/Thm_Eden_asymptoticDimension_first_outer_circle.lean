-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_first_outer_circle
-- name    : Eden.asymptoticDimension_first_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:23.160909+00:00
-- url     : https://prove2.me/theorems/2901f05c-a0ae-5704-99a7-947159d2aebb
-- title:
--   Eden: asymptotic Dimension first outer circle
-- statement:
--   The Eden construction uses the asymptotic Dimension first outer circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L109-L114
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L109-L114

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_first_outer_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2) : asymptoticDimension c p = 1 := by sorry
