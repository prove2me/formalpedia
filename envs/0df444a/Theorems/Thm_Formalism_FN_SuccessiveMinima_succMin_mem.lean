-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_succMin_mem
-- name    : Formalism.FN.SuccessiveMinima.succMin_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:26.180441+00:00
-- url     : https://prove2.me/theorems/758f3abf-bf46-469b-ba5f-b58cafef6741
-- title:
--   Successive Minima: succ Min mem
-- statement:
--   The Successive Minima construction uses the succ Min mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L55-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L55-L86

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.FN Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}

theorem Formalism.FN.SuccessiveMinima.succMin_mem (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K)
    {i : ℕ} {T : ℝ}
    (hT : 0 ≤ T ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K))) :
    0 ≤ succMin L K i ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K i • K)) := by sorry
