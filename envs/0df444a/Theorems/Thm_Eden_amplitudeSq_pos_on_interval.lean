-- Prove2me | Theorems.Thm_Eden_amplitudeSq_pos_on_interval
-- name    : Eden.amplitudeSq_pos_on_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:16:19.734575+00:00
-- url     : https://prove2.me/theorems/32e3994a-0317-41a4-8cde-846ce0280f03
-- title:
--   Eden: amplitude Sq pos on interval
-- statement:
--   The Eden construction uses the amplitude Sq pos on interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L16-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/CompleteTrajectories.lean#L16-L40

import Definitions.Def_Eden_Evolution
import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_CompleteTrajectories
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.amplitudeSq_pos_on_interval (t : ℝ) {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) :
    0 < amplitudeSq t s := by sorry
