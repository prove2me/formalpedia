-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_up
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.up
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:36.449798+00:00
-- url     : https://prove2.me/theorems/c3731572-528d-4367-8294-e54b83d21fb2
-- title:
--   Pieri: up
-- statement:
--   The Pieri construction uses the up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L281-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L281-L313

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.up (n : ℕ) : ∀ (μ : Fin n → ℤ) (b : ℕ), Antitone μ →
    ∑ ν ∈ stripsUp μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by sorry
