-- Prove2me | Theorems.Thm_Formalism_Pfun_ne_zero_of_one_le_re
-- name    : Formalism.Pfun_ne_zero_of_one_le_re
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:58.124352+00:00
-- url     : https://prove2.me/theorems/47defdc3-be9f-4cb6-a8d8-8214d76a300e
-- title:
--   Formalism: Pfun ne zero of one le re
-- statement:
--   The Formalism construction uses the Pfun ne zero of one le re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L19-L26

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem Formalism.Pfun_ne_zero_of_one_le_re (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : Pfun χ s ≠ 0 := by sorry
