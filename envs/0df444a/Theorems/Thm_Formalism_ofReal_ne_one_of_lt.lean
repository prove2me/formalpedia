-- Prove2me | Theorems.Thm_Formalism_ofReal_ne_one_of_lt
-- name    : Formalism.ofReal_ne_one_of_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:07.136965+00:00
-- url     : https://prove2.me/theorems/6eeebc83-deb8-4603-980f-4330e2ca847a
-- title:
--   Formalism: of Real ne one of lt
-- statement:
--   The Formalism construction uses the of Real ne one of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L20-L24

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

theorem Formalism.ofReal_ne_one_of_lt {σ : ℝ} (h : σ < 1) : (σ : ℂ) ≠ 1 := by sorry
