-- Prove2me | Theorems.Thm_Eden_evolution_mem_attractor
-- name    : Eden.evolution_mem_attractor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:25.009679+00:00
-- url     : https://prove2.me/theorems/f7b6724e-4abe-4e55-a8ad-18c608ced50f
-- title:
--   Eden: evolution mem attractor
-- statement:
--   The Eden construction uses the evolution mem attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L38-L46
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InvariantSets.lean#L38-L46

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.evolution_mem_attractor (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) : evolution c t p ∈ attractor := by sorry
