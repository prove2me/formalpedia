-- Prove2me | Theorems.Thm_Formalism_ZF_lamF_anti
-- name    : Formalism.ZF.lamF_anti
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:21.382466+00:00
-- url     : https://prove2.me/theorems/b7b99172-1b8b-4021-b609-67863403def5
-- title:
--   ZF: lam F anti
-- statement:
--   The ZF construction uses the lam F anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L39-L50

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by sorry
