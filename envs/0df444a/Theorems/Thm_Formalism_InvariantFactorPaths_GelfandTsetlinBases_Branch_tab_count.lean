-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Branch_tab_count
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.tab_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:20.920004+00:00
-- url     : https://prove2.me/theorems/1bb9c410-9891-4aff-9d34-d6ff7a67d4f1
-- title:
--   Branch: tab count
-- statement:
--   The Branch construction uses the tab count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L411-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/Branch.lean#L411-L474

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_Branch
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Branch.tab_count (n : ℕ) : ∀ μ : Fin n → ℤ, Antitone μ →
    Finite {T : ℤ → Finset (Fin n) // TabP μ T} ∧
      Nat.card {T : ℤ → Finset (Fin n) // TabP μ T} = dGT n μ := by sorry
