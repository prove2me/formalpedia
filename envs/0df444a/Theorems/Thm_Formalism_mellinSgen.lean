-- Prove2me | Theorems.Thm_Formalism_mellinSgen
-- name    : Formalism.mellinSgen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:32.121342+00:00
-- url     : https://prove2.me/theorems/a996d7f7-3130-479f-a979-b1fda304e036
-- title:
--   Formalism: mellin Sgen
-- statement:
--   The Formalism construction uses the mellin Sgen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L101-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L101-L172

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

theorem Formalism.mellinSgen : MellinSgen := by sorry
