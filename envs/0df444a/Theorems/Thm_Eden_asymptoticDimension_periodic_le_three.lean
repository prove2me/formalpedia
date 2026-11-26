-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_periodic_le_three
-- name    : Eden.asymptoticDimension_periodic_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:14.694462+00:00
-- url     : https://prove2.me/theorems/f0cef679-ee5c-5ca1-9a15-7ab33b57da31
-- title:
--   Eden: asymptotic Dimension periodic le three
-- statement:
--   The Eden construction uses the asymptotic Dimension periodic le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L154-L162
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L154-L162

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_periodic_le_three {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) : asymptoticDimension c p ≤ 3 := by sorry
