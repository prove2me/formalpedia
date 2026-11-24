-- Prove2me | Theorems.Thm_Formalism_mxS_nonneg
-- name    : Formalism.mxS_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:18.526124+00:00
-- url     : https://prove2.me/theorems/feaf1679-553b-4799-9b88-2b55e2cc1c8a
-- title:
--   Formalism: mx S nonneg
-- statement:
--   The Formalism construction uses the mx S nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinSAux.lean#L11-L13

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
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

theorem Formalism.mxS_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by sorry
