-- Prove2me | Theorems.Thm_Eden_divergence_neg
-- name    : Eden.divergence_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:26:10.73026+00:00
-- url     : https://prove2.me/theorems/d83d4c1d-5d3c-4ff3-9f49-6b0c1b81c937
-- title:
--   Eden: divergence neg
-- statement:
--   The Eden construction uses the divergence neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L41-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L41-L42

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.divergence_neg {c : ℝ} (hc : 4 < c) (p : PhaseSpace) : divergence c p < 0 := by sorry
