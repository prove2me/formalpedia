-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_cond_low
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:08.263802+00:00
-- url     : https://prove2.me/theorems/53760d0e-0b6a-4304-99a9-5a929d00177f
-- title:
--   Pieri: cond low
-- statement:
--   The Pieri construction uses the cond low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L189-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L189-L198

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_low {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    (κ ∈ gtBox μ ∧ l ∈ sLe κ b) ↔
      (∀ i, Lo μ l i.succ ≤ κ i) ∧ (∀ i, κ i ≤ Hi μ l i) ∧ ∑ i, l i - ∑ i, κ i ≤ (b : ℤ) := by sorry
