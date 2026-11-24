-- Prove2me | Theorems.Thm_Formalism_summable_a_mxS
-- name    : Formalism.summable_a_mxS
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:40.482853+00:00
-- url     : https://prove2.me/theorems/2b5cb6ad-b29c-4206-863f-5267f6fc4cc1
-- title:
--   Formalism: summable a mx S
-- statement:
--   The Formalism construction uses the summable a mx S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L64-L65

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
variable (a : ℕ → ℝ)

theorem Formalism.summable_a_mxS (ha0 : a 0 = 0) (x : ℝ) : Summable (fun n => a n * mxS n x) := by sorry
