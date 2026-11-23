-- Prove2me | Theorems.Thm_Formalism_FN_GjScaling_mem_span_basisFun_iff
-- name    : Formalism.FN.GjScaling.mem_span_basisFun_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:23.777784+00:00
-- url     : https://prove2.me/theorems/1673113d-a0bd-4107-9987-b9b372211b95
-- title:
--   Gj Scaling: mem span basis Fun iff
-- statement:
--   The Gj Scaling construction uses the mem span basis Fun iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/GjScale.lean#L35-L46

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

theorem Formalism.FN.GjScaling.mem_span_basisFun_iff (x : ι → ℝ) :
    x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ x ∈ Zv ι := by sorry
