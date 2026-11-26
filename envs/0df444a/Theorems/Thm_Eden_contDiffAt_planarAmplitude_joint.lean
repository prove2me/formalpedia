-- Prove2me | Theorems.Thm_Eden_contDiffAt_planarAmplitude_joint
-- name    : Eden.contDiffAt_planarAmplitude_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:29.776346+00:00
-- url     : https://prove2.me/theorems/abf0beac-6cae-4f6e-ad75-7490c6a3b324
-- title:
--   Eden: cont Diff At planar Amplitude joint
-- statement:
--   The Eden construction uses the cont Diff At planar Amplitude joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L30-L34
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L30-L34

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiffAt_planarAmplitude_joint {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => planarAmplitude u.1 u.2) (t, s) := by sorry
