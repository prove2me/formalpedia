-- Prove2me | Theorems.Thm_Eden_continuousOn_evolution
-- name    : Eden.continuousOn_evolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:38.999438+00:00
-- url     : https://prove2.me/theorems/9535fbe5-f7a5-4290-9039-cf341a3740d7
-- title:
--   Eden: continuous On evolution
-- statement:
--   The Eden construction uses the continuous On evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L47-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Uniqueness.lean#L47-L49

import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_Uniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuousOn_evolution (c : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun t => evolution c t p) (Ici 0) := by sorry
