-- Prove2me | Theorems.Thm_Eden_isCompact_torus
-- name    : Eden.isCompact_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:57.054267+00:00
-- url     : https://prove2.me/theorems/cf8291a5-355c-4c63-9037-03c0abb934f7
-- title:
--   Eden: is Compact torus
-- statement:
--   The Eden construction uses the is Compact torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L90-L91
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L90-L91

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isCompact_torus : IsCompact torus := by sorry
