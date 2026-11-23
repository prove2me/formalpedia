-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_finite_lat_inter
-- name    : Formalism.FN.SuccessiveMinima.finite_lat_inter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:38.903839+00:00
-- url     : https://prove2.me/theorems/bf5f5cae-4c4d-4ced-a399-37c3c4eb526c
-- title:
--   Successive Minima: finite lat inter
-- statement:
--   The Successive Minima construction uses the finite lat inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L33-L42

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

theorem Formalism.FN.SuccessiveMinima.finite_lat_inter (L : Submodule ℤ E) [DiscreteTopology L] {s : Set E}
    (hs : Bornology.IsBounded s) : ((L : Set E) ∩ s).Finite := by sorry
