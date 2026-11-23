-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_sum
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:41.314957+00:00
-- url     : https://prove2.me/theorems/d256ae46-d27c-41b0-b01f-2c7afacf3ab4
-- title:
--   Lead At: sum
-- statement:
--   The Lead At construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L114-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L114-L130

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
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.sum {ι : Type*} {w : σ → M} (T : Finset ι) (v : ι → M) (t : ι → MvPolynomial σ R)
    (ht : ∀ m ∈ T, IsWeightedHomogeneous w (t m) (v m)) (top : ι) (htop : top ∈ T)
    (hlt : ∀ m ∈ T, m ≠ top → v m < v top) : LeadAt w (v top) (∑ m ∈ T, t m) (t top) := by sorry
