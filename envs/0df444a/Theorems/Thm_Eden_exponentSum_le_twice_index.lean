-- Prove2me | Theorems.Thm_Eden_exponentSum_le_twice_index
-- name    : Eden.exponentSum_le_twice_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:17.136532+00:00
-- url     : https://prove2.me/theorems/6c43706d-bf34-4137-9ff2-d3e225f41f86
-- title:
--   Eden: exponent Sum le twice index
-- statement:
--   The Eden construction uses the exponent Sum le twice index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L82-L92
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L82-L92

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_le_twice_index {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (k : ℕ) : spectrumPartialSum (lyapunovExponent c p) k ≤ (k : ℝ) * 2 := by sorry
