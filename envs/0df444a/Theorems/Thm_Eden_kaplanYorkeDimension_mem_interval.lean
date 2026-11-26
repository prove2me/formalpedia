-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_mem_interval
-- name    : Eden.kaplanYorkeDimension_mem_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:58.829361+00:00
-- url     : https://prove2.me/theorems/fa655a82-caf1-4018-8bc7-c9ebeb9277f7
-- title:
--   Eden: kaplan Yorke Dimension mem interval
-- statement:
--   The Eden construction uses the kaplan Yorke Dimension mem interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L126-L140
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean#L126-L140

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_mem_interval (a : Fin 5 → ℝ) :
    kaplanYorkeDimension a ∈ Set.Icc 0 5 := by sorry
