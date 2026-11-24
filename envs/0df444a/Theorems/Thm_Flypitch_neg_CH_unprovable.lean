-- Prove2me | Theorems.Thm_Flypitch_neg_CH_unprovable
-- name    : Flypitch.neg_CH_unprovable
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:02:06.775903+00:00
-- url     : https://prove2.me/theorems/8f0931a5-082a-4d02-aa85-80380470979e
-- title:
--   The negation of CH is not provable from ZFC
-- statement:
--   The **negation** of the continuum hypothesis is **not provable** from ZFC: $$\neg\,(\mathrm{ZFC} \vdash \neg\,\mathrm{CH}_f).$$ This is the other half of the independence — the Gödel direction, showing that CH cannot be refuted from ZFC. Together with the unprovability of CH it yields the independence of CH.
--
--   **Formalization Note.** The negation of the sentence `CH_f` is written `bd_not CH_f`, ascribed to `sentence L_ZFC`.
-- source:
--   J. M. Han and F. van Doorn, Flypitch project, src/summary.lean (https://github.com/flypitch/flypitch/blob/master/src/summary.lean); Lean 4 port https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean ; cf. Han–van Doorn, 'A Formal Proof of the Independence of the Continuum Hypothesis', CPP 2020, https://doi.org/10.1145/3372885.3373826 . Theorem `neg_CH_unprovable` in summary.lean.

import Definitions.Def_CH_Cohen_Library10
open Fol

namespace Flypitch
theorem neg_CH_unprovable : ¬ (ZFC ⊢ₛ' (bd_not CH_f : sentence L_ZFC)) := by sorry
end Flypitch
