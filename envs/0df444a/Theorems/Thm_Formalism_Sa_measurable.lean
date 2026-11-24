-- Prove2me | Theorems.Thm_Formalism_Sa_measurable
-- name    : Formalism.Sa_measurable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:28:43.955731+00:00
-- url     : https://prove2.me/theorems/8642347f-bcef-4f44-bf7f-6774046f430c
-- title:
--   Formalism: Sa measurable
-- statement:
--   The Formalism construction uses the Sa measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L13-L28

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

theorem Formalism.Sa_measurable : Measurable (Sa a) := by sorry
