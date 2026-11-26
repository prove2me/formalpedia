-- Prove2me | Theorems.Thm_Eden_divergence_le
-- name    : Eden.divergence_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:18.375247+00:00
-- url     : https://prove2.me/theorems/2d524ab3-2d67-4844-9b27-7e5ac8b3311c
-- title:
--   Eden: divergence le
-- statement:
--   The Eden construction uses the divergence le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L37-L39
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L37-L39

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.divergence_le (c : ℝ) (p : PhaseSpace) : divergence c p ≤ 4 - c := by sorry
