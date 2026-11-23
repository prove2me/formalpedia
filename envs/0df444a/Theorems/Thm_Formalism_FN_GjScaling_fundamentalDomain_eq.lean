-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_fundamentalDomain_eq
-- name    : Formalism.FN.GjScaling.fundamentalDomain_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:59.987552+00:00
-- url     : https://prove2.me/theorems/65c9308d-8e2b-454a-9ce2-624c7ca3ee26
-- title:
--   Gj Scaling: fundamental Domain eq
-- statement:
--   The Gj Scaling construction uses the fundamental Domain eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L48-L50

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]

theorem Formalism.FN.GjScaling.fundamentalDomain_eq : ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Qv ι := by sorry
