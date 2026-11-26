-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_second_outer_circle
-- name    : Eden.asymptoticDimension_second_outer_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:37.665799+00:00
-- url     : https://prove2.me/theorems/f6ba8b5f-b570-4a24-b78b-5486e93365b7
-- title:
--   Eden: asymptotic Dimension second outer circle
-- statement:
--   The Eden construction uses the asymptotic Dimension second outer circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L116-L120
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L116-L120

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_second_outer_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2) : asymptoticDimension c p = 1 := by sorry
