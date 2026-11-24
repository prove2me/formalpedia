-- Prove2me | Theorems.Thm_Flypitch_ZFC_is_consistent
-- name    : Flypitch.ZFC_is_consistent
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:00:40.218943+00:00
-- url     : https://prove2.me/theorems/8fc7e83b-2264-4d2c-824b-051919743830
-- title:
--   ZFC is consistent
-- statement:
--   The **consistency of ZFC**, witnessed by a Boolean-valued model. For every nontrivial complete Boolean algebra $\beta$, the theory ZFC is consistent — it does not prove falsum: $$\mathrm{ZFC}\ \text{is consistent}.$$ Because $V\,\beta$ is a Boolean-valued model of ZFC (the fundamental theorem of forcing), ZFC cannot prove a contradiction. The statement is parameterized by a nontrivial complete Boolean algebra $\beta$, mirroring the source.
--
--   **Formalization Note.** Consistency is `SentTheory.is_consistent`, i.e. `¬ (ZFC.fst ⊢' ⊥')`.
-- source:
--   J. M. Han and F. van Doorn, Flypitch project, src/summary.lean (https://github.com/flypitch/flypitch/blob/master/src/summary.lean); Lean 4 port https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean ; cf. Han–van Doorn, 'A Formal Proof of the Independence of the Continuum Hypothesis', CPP 2020, https://doi.org/10.1145/3372885.3373826 . Theorem `ZFC_is_consistent` in summary.lean.

import Definitions.Def_CH_Cohen_Library10
open Fol

namespace Flypitch
theorem ZFC_is_consistent {β : Type 0} [NontrivialCompleteBooleanAlgebra β] :
    SentTheory.is_consistent ZFC := by sorry
end Flypitch
