-- Prove2me | Theorems.Thm_Flypitch_independence_of_CH
-- name    : Flypitch.independence_of_CH
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T22:02:42.900157+00:00
-- url     : https://prove2.me/theorems/d1aa5955-7cb8-4308-be1d-50040afdce08
-- title:
--   Independence of the continuum hypothesis from ZFC
-- statement:
--   The marquee theorem: the continuum hypothesis is **independent** of ZFC. Neither CH nor its negation is provable from the ZFC axioms: $$\mathrm{independent}(\mathrm{ZFC}, \mathrm{CH}_f) \;=\; \neg\,(\mathrm{ZFC} \vdash \mathrm{CH}_f)\ \wedge\ \neg\,(\mathrm{ZFC} \vdash \neg\,\mathrm{CH}_f).$$ This combines the two unprovability results and is the central result of the Flypitch project — a machine-checked proof that the continuum hypothesis can neither be proved nor disproved from the standard axioms of set theory.
--
--   **Formalization Note.** Stated via the definition `Flypitch.independent`; the two conjuncts are `Flypitch.CH_unprovable` and `Flypitch.neg_CH_unprovable`.
-- source:
--   J. M. Han and F. van Doorn, Flypitch project, src/summary.lean (https://github.com/flypitch/flypitch/blob/master/src/summary.lean); Lean 4 port https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Summary.lean ; cf. Han–van Doorn, 'A Formal Proof of the Independence of the Continuum Hypothesis', CPP 2020, https://doi.org/10.1145/3372885.3373826 . Theorem `independence_of_CH` in summary.lean (the goal).

import Definitions.Def_CH_Cohen_Library10
import Definitions.Def_Flypitch_independent
open Fol

namespace Flypitch
theorem independence_of_CH : independent ZFC CH_f := by sorry
end Flypitch
