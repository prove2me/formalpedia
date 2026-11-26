-- Prove2me | Theorems.Thm_Eden_exponentSum_image_bddAbove
-- name    : Eden.exponentSum_image_bddAbove
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:03.747103+00:00
-- url     : https://prove2.me/theorems/4f2098df-8919-46bb-90d7-b04effaba8dc
-- title:
--   Eden: exponent Sum image bdd Above
-- statement:
--   The Eden construction uses the exponent Sum image bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L98-L102
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L98-L102

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_image_bddAbove {c : ℝ} (hc : 4 < c) (k : ℕ) :
    BddAbove ((fun p => spectrumPartialSum (lyapunovExponent c p) k) '' attractor) := by sorry
