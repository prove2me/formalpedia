-- Prove2me | Theorems.Thm_Eden_exponentSum_five
-- name    : Eden.exponentSum_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:08.23281+00:00
-- url     : https://prove2.me/theorems/f7694331-3fa7-48c5-96a5-c79b2289d3ca
-- title:
--   Eden: exponent Sum five
-- statement:
--   The Eden construction uses the exponent Sum five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L70-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L70-L74

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.exponentSum_five {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    spectrumPartialSum (lyapunovExponent c p) 5 =
      spectrumPartialSum (lyapunovExponent c p) 4 - c := by sorry
