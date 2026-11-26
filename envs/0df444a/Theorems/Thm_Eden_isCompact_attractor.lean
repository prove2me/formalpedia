-- Prove2me | Theorems.Thm_Eden_isCompact_attractor
-- name    : Eden.isCompact_attractor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:52.045835+00:00
-- url     : https://prove2.me/theorems/2c3b213f-056a-5a6b-9a23-9ff514fa41c1
-- title:
--   Eden: is Compact attractor
-- statement:
--   The Eden construction uses the is Compact attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L85-L88
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L85-L88

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.isCompact_attractor : IsCompact attractor := by sorry
