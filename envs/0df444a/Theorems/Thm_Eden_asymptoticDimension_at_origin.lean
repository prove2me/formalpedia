-- Prove2me | Theorems.Thm_Eden_asymptoticDimension_at_origin
-- name    : Eden.asymptoticDimension_at_origin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:53.100863+00:00
-- url     : https://prove2.me/theorems/ecb1d992-c803-55ab-9a37-49f72ee4e2b1
-- title:
--   Eden: asymptotic Dimension at origin
-- statement:
--   The Eden construction uses the asymptotic Dimension at origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L90-L94
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicDimensions.lean#L90-L94

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.asymptoticDimension_at_origin {c : ℝ} (hc : 4 < c) :
    asymptoticDimension c 0 = 0 := by sorry
