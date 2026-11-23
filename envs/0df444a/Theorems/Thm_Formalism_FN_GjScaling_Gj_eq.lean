-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_Gj_eq
-- name    : Formalism.FN.GjScaling.Gj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:41.884767+00:00
-- url     : https://prove2.me/theorems/47f29fc0-fea0-42dc-8f2f-9959b09fb540
-- title:
--   Gj Scaling: Gj eq
-- statement:
--   The Gj Scaling construction uses the Gj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L187-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L187-L199

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
variable (n j : ℕ)

theorem Formalism.FN.GjScaling.Gj_eq (A : Set (Fin n → ℝ)) (hA : IsOpen A) :
    Gj n j A = ∫⁻ y, tm (fib n j A y) := by sorry
