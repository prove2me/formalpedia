-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_antitone_of_mem_gtBox
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.antitone_of_mem_gtBox
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.768804+00:00
-- url     : https://prove2.me/theorems/3b8e4def-9c5d-4b20-be7e-8843c8e45149
-- title:
--   Pieri: antitone of mem gt Box
-- statement:
--   The Pieri construction uses the antitone of mem gt Box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L49-L57

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.antitone_of_mem_gtBox {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ)
    (hκ : κ ∈ gtBox μ) : Antitone κ := by sorry
