-- Prove2me | Theorems.Thm_Eden_firstCircle_ne_firstCircle
-- name    : Eden.firstCircle_ne_firstCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:29.836424+00:00
-- url     : https://prove2.me/theorems/9dec7ef0-48a7-4961-9f3a-42c33bd558f6
-- title:
--   Eden: first Circle ne first Circle
-- statement:
--   The Eden construction uses the first Circle ne first Circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicOrbits.lean#L27-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicOrbits.lean#L27-L32

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.firstCircle_ne_firstCircle {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≠ u) :
    firstCircle s ≠ firstCircle u := by sorry
