-- Prove2me | Theorems.Thm_Eden_kaplanYorkeIndex_eq_of_adjacent_signs
-- name    : Eden.kaplanYorkeIndex_eq_of_adjacent_signs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:24.925796+00:00
-- url     : https://prove2.me/theorems/aeb98647-e74f-5c49-b56e-8ca85632d6ed
-- title:
--   Eden: kaplan Yorke Index eq of adjacent signs
-- statement:
--   The Eden construction uses the kaplan Yorke Index eq of adjacent signs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L49-L57
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/EventualDimensionFormulas.lean#L49-L57

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.kaplanYorkeIndex_eq_of_adjacent_signs {a : Fin 5 → ℝ} (ha : Antitone a)
    {k : ℕ} (hk : k < 5) (h₀ : 0 ≤ spectrumPartialSum a k)
    (h₁ : spectrumPartialSum a (k + 1) < 0) : kaplanYorkeIndex a = k := by sorry
