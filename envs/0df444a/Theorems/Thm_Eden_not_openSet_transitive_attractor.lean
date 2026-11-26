-- Prove2me | Theorems.Thm_Eden_not_openSet_transitive_attractor
-- name    : Eden.not_openSet_transitive_attractor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:45:17.017544+00:00
-- url     : https://prove2.me/theorems/456c8058-e4d5-51de-bd21-c2d63cdfd7cf
-- title:
--   Eden: not open Set transitive attractor
-- statement:
--   Failure of the open-set formulation of topological transitivity, with all
--   nonnegative real times allowed.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L139-L152
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L139-L152

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.not_openSet_transitive_attractor (c : ℝ) :
    ¬ (∀ U V : Set attractor, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
      ∃ (t : ℝ) (ht : 0 ≤ t) (p : attractor), p ∈ U ∧ attractorEvolution c ht p ∈ V) := by sorry
