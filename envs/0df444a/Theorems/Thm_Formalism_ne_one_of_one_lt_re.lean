-- Prove2me | Theorems.Thm_Formalism_ne_one_of_one_lt_re
-- name    : Formalism.ne_one_of_one_lt_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:20.668998+00:00
-- url     : https://prove2.me/theorems/e114f0bc-3dd0-45c5-8450-3e9f01210443
-- title:
--   Formalism: ne one of one lt re
-- statement:
--   The Formalism construction uses the ne one of one lt re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L148-L150

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

theorem Formalism.ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by sorry
