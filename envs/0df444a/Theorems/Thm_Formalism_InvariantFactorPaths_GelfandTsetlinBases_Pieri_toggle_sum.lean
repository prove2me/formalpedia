-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_toggle_sum
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.toggle_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:07.772466+00:00
-- url     : https://prove2.me/theorems/ba8b3b93-aaad-4de9-bd55-26cbf022e41d
-- title:
--   Pieri: toggle sum
-- statement:
--   The Pieri construction uses the toggle sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L222-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L222-L272

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.toggle_sum {n : ℕ} (μ : Fin (n + 1) → ℤ) (b : ℕ) (f : (Fin n → ℤ) → ℕ) :
    ∑ ν ∈ stripsUp μ b, ∑ l ∈ gtBox ν, f l = ∑ κ ∈ gtBox μ, ∑ l ∈ sLe κ b, f l := by sorry
