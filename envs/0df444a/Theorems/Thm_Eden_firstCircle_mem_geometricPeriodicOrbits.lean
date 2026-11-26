-- Prove2me | Theorems.Thm_Eden_firstCircle_mem_geometricPeriodicOrbits
-- name    : Eden.firstCircle_mem_geometricPeriodicOrbits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:09.555073+00:00
-- url     : https://prove2.me/theorems/64e68062-05fa-5af5-8e63-995cc1f22df2
-- title:
--   Eden: first Circle mem geometric Periodic Orbits
-- statement:
--   The Eden construction uses the first Circle mem geometric Periodic Orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicOrbits.lean#L48-L58
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicOrbits.lean#L48-L58

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.firstCircle_mem_geometricPeriodicOrbits {c s : ℝ} (hc : 0 < c)
    (hs : s = 1 ∨ s = 2) : firstCircle s ∈ geometricPeriodicOrbits c := by sorry
