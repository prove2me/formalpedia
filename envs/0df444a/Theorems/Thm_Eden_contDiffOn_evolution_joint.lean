-- Prove2me | Theorems.Thm_Eden_contDiffOn_evolution_joint
-- name    : Eden.contDiffOn_evolution_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:50.598725+00:00
-- url     : https://prove2.me/theorems/a6bccfb6-c5d7-5ee4-8845-a16aadb6ca53
-- title:
--   Eden: cont Diff On evolution joint
-- statement:
--   The Eden construction uses the cont Diff On evolution joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L53-L57
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L53-L57

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiffOn_evolution_joint (c : ℝ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun u : ℝ × PhaseSpace => evolution c u.1 u.2)
      {u | 0 ≤ u.1} := by sorry
