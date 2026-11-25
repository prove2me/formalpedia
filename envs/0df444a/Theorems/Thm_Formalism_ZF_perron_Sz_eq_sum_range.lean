-- Prove2me | Theorems.Thm_Formalism_ZF_perron_Sz_eq_sum_range
-- name    : Formalism.ZF.perron_Sz_eq_sum_range
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:40.918826+00:00
-- url     : https://prove2.me/theorems/bf80fa21-55f1-424e-95e3-062f1a079b4c
-- title:
--   ZF: perron Sz eq sum range
-- statement:
--   The ZF construction uses the perron Sz eq sum range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L31-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/Perron.lean#L31-L42

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.perron_Sz_eq_sum_range {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sz x = ∑ n ∈ Finset.range N, Λ n * Formalism.mxS n x := by sorry
