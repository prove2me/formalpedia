-- Prove2me | Theorems.Thm_Formalism_abs_Sa_le
-- name    : Formalism.abs_Sa_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:20.334307+00:00
-- url     : https://prove2.me/theorems/0534c468-9396-4b6e-bf82-f534b0a2067b
-- title:
--   Formalism: abs Sa le
-- statement:
--   The Formalism construction uses the abs Sa le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSgen.lean#L67-L76

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

theorem Formalism.abs_Sa_le (ha0 : a 0 = 0) (x : ℝ) : |Sa a x| ≤ ∑' n, |a n| * mxS n x := by sorry
