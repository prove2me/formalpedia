-- Prove2me | Theorems.Thm_Eden_contDiff_evolution
-- name    : Eden.contDiff_evolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:51.02537+00:00
-- url     : https://prove2.me/theorems/b427e956-806c-4ed4-a8b5-ccb43d5bf46a
-- title:
--   Eden: cont Diff evolution
-- statement:
--   Smooth dependence on all five ambient coordinates, in the Euclidean norm.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L79-L101
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/InitialDerivative.lean#L79-L101

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_InitialDerivative
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiff_evolution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (n : WithTop ℕ∞) :
    ContDiff ℝ n (evolution c t) := by sorry
