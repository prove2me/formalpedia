-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_prod
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:32.937959+00:00
-- url     : https://prove2.me/theorems/5db5f45b-948e-45fb-b5ff-9ba559de11e2
-- title:
--   Lead At: prod
-- statement:
--   The Lead At construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L89-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L89-L101

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.prod {ι : Type*} {w : σ → M} (s : Finset ι) (γ : ι → M) (f t : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, LeadAt w (γ i) (f i) (t i)) :
    LeadAt w (∑ i ∈ s, γ i) (∏ i ∈ s, f i) (∏ i ∈ s, t i) := by sorry
