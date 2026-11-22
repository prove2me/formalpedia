-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_mem_smul_iff_gauge
-- name    : Formalism.FN.SuccessiveMinima.mem_smul_iff_gauge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:49.039207+00:00
-- url     : https://prove2.me/theorems/77a0804d-8936-4c5d-a7d6-e30bf5e0514c
-- title:
--   Successive Minima: mem smul iff gauge
-- statement:
--   The Successive Minima construction uses the mem smul iff gauge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L12-L31

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

theorem Formalism.FN.SuccessiveMinima.mem_smul_iff_gauge {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 ≤ t) (u : E) :
    u ∈ t • K ↔ gauge K u ≤ t := by sorry
