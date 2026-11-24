-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_strip_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.strip_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:02.47113+00:00
-- url     : https://prove2.me/theorems/70d3d587-63dc-446a-a8c6-64fc60a62e8a
-- title:
--   A1: strip iff
-- statement:
--   The A1 construction uses the strip iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L528-L549
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L528-L549

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.strip_iff {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (hν : Antitone ν) (hμ : Antitone μ)
    (hs : HStrip ν μ b) (c : ℤ) (m : Fin n) :
    (colHeight ν c ≠ colHeight μ c ∧ m.val = min (colHeight ν c) (colHeight μ c)) ↔
      c ∈ Finset.Ioc (μ m) (ν m) := by sorry
