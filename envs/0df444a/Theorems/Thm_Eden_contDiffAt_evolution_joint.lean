-- Prove2me | Theorems.Thm_Eden_contDiffAt_evolution_joint
-- name    : Eden.contDiffAt_evolution_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:33.372318+00:00
-- url     : https://prove2.me/theorems/8f098efd-4fb7-5e55-af84-767e7767866a
-- title:
--   Eden: cont Diff At evolution joint
-- statement:
--   Smoothness in time and all five ambient coordinates jointly, at every
--   nonnegative time, with no restriction on the initial point or parameter.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L38-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L38-L51

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiffAt_evolution_joint (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2) (t, p) := by sorry
