-- Prove2me | Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one
-- name    : Formalism.riemannZetaOne_eq_mul_of_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:27.307376+00:00
-- url     : https://prove2.me/theorems/37494f16-d59c-4994-b500-aabdc46cf7b2
-- title:
--   Formalism: riemann Zeta One eq mul of ne one
-- statement:
--   The Formalism construction uses the riemann Zeta One eq mul of ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L9-L12

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

theorem Formalism.riemannZetaOne_eq_mul_of_ne_one {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by sorry
