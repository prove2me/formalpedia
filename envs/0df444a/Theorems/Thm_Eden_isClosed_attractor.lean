-- Prove2me | Theorems.Thm_Eden_isClosed_attractor
-- name    : Eden.isClosed_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:27.676164+00:00
-- url     : https://prove2.me/theorems/0e0fd63f-1a8c-5db0-a200-ef8b67ef1156
-- title:
--   Eden: is Closed attractor
-- statement:
--   The Eden construction uses the is Closed attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L60-L64
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L60-L64

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isClosed_attractor : IsClosed attractor := by sorry
