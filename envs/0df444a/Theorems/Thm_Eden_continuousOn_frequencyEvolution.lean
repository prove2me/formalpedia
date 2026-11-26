-- Prove2me | Theorems.Thm_Eden_continuousOn_frequencyEvolution
-- name    : Eden.continuousOn_frequencyEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:40.788896+00:00
-- url     : https://prove2.me/theorems/fb3b461c-6366-503e-b152-895278aa6d1a
-- title:
--   Eden: continuous On frequency Evolution
-- statement:
--   The Eden construction uses the continuous On frequency Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L47-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FrequencyUniqueness.lean#L47-L49

import Definitions.Def_Eden_FrequencyEvolution
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Definitions.Def_Eden_FrequencyUniqueness
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.continuousOn_frequencyEvolution (c ν : ℝ) (p : PhaseSpace) :
    ContinuousOn (fun t => frequencyEvolution c ν t p) (Ici 0) := by sorry
