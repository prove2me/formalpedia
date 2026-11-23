-- Prove2me | Theorems.Thm_Formalism_sub_ne_zero_of_lt_re
-- name    : Formalism.sub_ne_zero_of_lt_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:09.570329+00:00
-- url     : https://prove2.me/theorems/7aca051f-7f80-48b2-9cf7-d1cf8138a5c0
-- title:
--   Formalism: sub ne zero of lt re
-- statement:
--   The Formalism construction uses the sub ne zero of lt re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L152-L156

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

theorem Formalism.sub_ne_zero_of_lt_re {s : ℂ} {a : ℝ} (hs : a < s.re) : s - a ≠ 0 := by sorry
