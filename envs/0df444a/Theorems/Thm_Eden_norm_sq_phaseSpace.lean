-- Prove2me | Theorems.Thm_Eden_norm_sq_phaseSpace
-- name    : Eden.norm_sq_phaseSpace
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:39.535162+00:00
-- url     : https://prove2.me/theorems/d7b0190b-6208-5d01-8f88-00183b003c53
-- title:
--   Eden: norm sq phase Space
-- statement:
--   The Eden construction uses the norm sq phase Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L72-L76
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L72-L76

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.norm_sq_phaseSpace (p : PhaseSpace) :
    ‖p‖ ^ 2 = radiusSq₁ p + radiusSq₂ p + p 4 ^ 2 := by sorry
