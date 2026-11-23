-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_pos_bot
-- name    : Formalism.FN.SuccessiveMinima.exists_pos_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:13.724159+00:00
-- url     : https://prove2.me/theorems/d9d88dd1-1d1f-44e0-ad68-fed620a38762
-- title:
--   Successive Minima: exists pos bot
-- statement:
--   The Successive Minima construction uses the exists pos bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L88-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L88-L105

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

theorem Formalism.FN.SuccessiveMinima.exists_pos_bot (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → t < m →
      Submodule.span ℝ ((L : Set E) ∩ t • K) = ⊥ := by sorry
