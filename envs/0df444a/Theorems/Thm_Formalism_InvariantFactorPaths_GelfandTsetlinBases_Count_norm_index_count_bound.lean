-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_norm_index_count_bound
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.norm_index_count_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:04.269605+00:00
-- url     : https://prove2.me/theorems/14f2b475-7abe-42de-aae1-47b3bfbeb560
-- title:
--   Count: norm index count bound
-- statement:
--   The Count construction uses the norm index count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/NormIndexCountBound.lean#L143-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/NormIndexCountBound.lean#L143-L177

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.norm_index_count_bound (hS : StripsMem) (hP : GTPieri) (hC : StdCountGT) (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) :
    ∀ (k i : ℕ), i + k = N → ∀ μ₀ : Fin n → ℤ, Antitone μ₀ →
      Finite (ContIdx n i N isVec B μ₀) ∧
      Nat.card (ContIdx n i N isVec B μ₀) = dGT n μ₀ * ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by sorry
