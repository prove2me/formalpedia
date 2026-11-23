-- Prove2me | Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_gap
-- name    : Formalism.FN.SuccessiveMinima.exists_gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:26.564324+00:00
-- url     : https://prove2.me/theorems/70db9cd5-d8f9-4d9d-844c-9fea413a319a
-- title:
--   Successive Minima: exists gap
-- statement:
--   The Successive Minima construction uses the exists gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/SuccMin.lean#L44-L51

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

theorem Formalism.FN.SuccessiveMinima.exists_gap {α : Type*} (f : α → ℝ) {B : Set α} (hB : B.Finite) {c T : ℝ} (hcT : c < T)
    (h : ∀ u ∈ B, c < f u) : ∃ m, c < m ∧ m ≤ T ∧ ∀ u ∈ B, m ≤ f u := by sorry
