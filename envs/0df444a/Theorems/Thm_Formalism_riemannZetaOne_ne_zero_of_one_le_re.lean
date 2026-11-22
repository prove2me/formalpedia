-- Prove2me | Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_one_le_re
-- name    : Formalism.riemannZetaOne_ne_zero_of_one_le_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:56.551552+00:00
-- url     : https://prove2.me/theorems/3d77a741-808b-4e13-a23d-8078377e04f4
-- title:
--   Formalism: riemann Zeta One ne zero of one le re
-- statement:
--   The Formalism construction uses the riemann Zeta One ne zero of one le re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L14-L18

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
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

theorem Formalism.riemannZetaOne_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by sorry
