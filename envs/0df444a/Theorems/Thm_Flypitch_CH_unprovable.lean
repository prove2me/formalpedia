-- Prove2me | Theorems.Thm_Flypitch_CH_unprovable
-- name    : Flypitch.CH_unprovable
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:01:22.229798+00:00
-- url     : https://prove2.me/theorems/4b505b5c-f04b-442f-8c0e-0f32e96794f6
-- title:
--   CH is not provable from ZFC
-- statement:
--   The continuum hypothesis is **not provable** from ZFC. Writing $\mathrm{CH}_f$ for the first-order sentence expressing the continuum hypothesis in the language of set theory, $$\neg\,(\mathrm{ZFC} \vdash \mathrm{CH}_f).$$ This is the Cohen direction of the independence: in the Cohen algebra the Boolean value of CH is strictly below $\top$, so CH is not forced, and by Boolean-valued soundness it is not provable.
--
--   **Formalization Note.** Provability is `SentTheory.sprovable` (notation `⊢ₛ'`); `CH_f` is the CH sentence and `ZFC` the ZFC theory from the library.
-- source:
--   J. M. Han and F. van Doorn, Flypitch project, src/summary.lean (https://github.com/flypitch/flypitch/blob/master/src/summary.lean); Lean 4 port https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean ; cf. Han–van Doorn, 'A Formal Proof of the Independence of the Continuum Hypothesis', CPP 2020, https://doi.org/10.1145/3372885.3373826 . Theorem `CH_unprovable` in summary.lean.

import Definitions.Def_CH_Cohen_Library10
open Fol

namespace Flypitch
theorem CH_unprovable : ¬ (ZFC ⊢ₛ' CH_f) := by sorry
end Flypitch
