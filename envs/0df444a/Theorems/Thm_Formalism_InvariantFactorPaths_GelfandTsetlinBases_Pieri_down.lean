-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_down
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.down
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:02.222691+00:00
-- url     : https://prove2.me/theorems/abb3a21f-6622-4a82-8993-221e18ee068f
-- title:
--   Pieri: down
-- statement:
--   The Pieri construction uses the down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L367-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L367-L377

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.down (n : ℕ) (μ : Fin n → ℤ) (b : ℕ) (hμ : Antitone μ) :
    ∑ ν ∈ stripsDown μ b, dGT n ν = dGT n μ * (n + b - 1).choose b := by sorry
