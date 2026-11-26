-- Prove2me | Theorems.Thm_Eden_contDiffAt_amplitudeSq_joint
-- name    : Eden.contDiffAt_amplitudeSq_joint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:30.442219+00:00
-- url     : https://prove2.me/theorems/ba854512-7006-45b9-886d-ecc2fa441237
-- title:
--   Eden: cont Diff At amplitude Sq joint
-- statement:
--   The Eden construction uses the cont Diff At amplitude Sq joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L15-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/JointSmoothness.lean#L15-L28

import Definitions.Def_Eden_InitialDerivative
import Definitions.Def_Eden_JointSmoothness
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.contDiffAt_amplitudeSq_joint {t s : ℝ} (hD : 0 < radialDiscriminant t s)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun u : ℝ × ℝ => amplitudeSq u.1 u.2) (t, s) := by sorry
