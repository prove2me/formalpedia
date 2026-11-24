-- Prove2me | Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_real_mem_Ioo
-- name    : Formalism.riemannZetaOne_ne_zero_of_real_mem_Ioo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:22.078061+00:00
-- url     : https://prove2.me/theorems/4e5bfae0-43a7-4198-9f5d-443b34b3d01a
-- title:
--   Formalism: riemann Zeta One ne zero of real mem Ioo
-- statement:
--   The Formalism construction uses the riemann Zeta One ne zero of real mem Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/RiemannZetaOneNeZeroOfRealMemIoo.lean#L26-L29

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

theorem Formalism.riemannZetaOne_ne_zero_of_real_mem_Ioo (h8 : ZetaRealNonvanish) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta₁ σ ≠ 0 := by sorry
