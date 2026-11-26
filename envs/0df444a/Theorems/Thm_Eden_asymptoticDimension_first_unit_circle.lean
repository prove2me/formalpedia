-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_first_unit_circle
-- name    : Eden.asymptoticDimension_first_unit_circle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:08.559046+00:00
-- url     : https://prove2.me/theorems/771beae6-b852-4da5-8746-8c366f1e33b3
-- title:
--   Eden: asymptotic Dimension first unit circle
-- statement:
--   The Eden construction uses the asymptotic Dimension first unit circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L96-L101
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L96-L101

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_first_unit_circle {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 1) : asymptoticDimension c p = 3 := by sorry
