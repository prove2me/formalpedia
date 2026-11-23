-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_span_top
-- name    : Formalism.FN.SuccessiveMinima.exists_span_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:58.280597+00:00
-- url     : https://prove2.me/theorems/3d2dfc6b-04d2-4538-9ab2-346327f15883
-- title:
--   Successive Minima: exists span top
-- statement:
--   The Successive Minima construction uses the exists span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L107-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L107-L119

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

theorem Formalism.FN.SuccessiveMinima.exists_span_top [IsZLattice ℝ L] (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) :
    ∃ T : ℝ, 0 ≤ T ∧ Submodule.span ℝ ((L : Set E) ∩ T • K) = ⊤ := by sorry
