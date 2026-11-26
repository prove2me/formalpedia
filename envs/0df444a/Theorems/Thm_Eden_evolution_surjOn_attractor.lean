-- Prove2me | Theorems.Thm_Eden_evolution_surjOn_attractor
-- name    : Eden.evolution_surjOn_attractor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:09:22.279305+00:00
-- url     : https://prove2.me/theorems/3cd2dab8-b10e-482b-936d-0e8dd1f47fa9
-- title:
--   Eden: evolution surj On attractor
-- statement:
--   The Eden construction uses the evolution surj On attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L62-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L62-L72

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.evolution_surjOn_attractor (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (evolution c t) attractor attractor := by sorry
