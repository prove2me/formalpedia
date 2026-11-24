-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_det_unit
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.det_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:23.126398+00:00
-- url     : https://prove2.me/theorems/fba77342-2c56-44e1-b17d-be700122be7a
-- title:
--   Minor Determinant Basis: det unit
-- statement:
--   The Minor Determinant Basis construction uses the det unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathBasisOfCount.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathBasisOfCount.lean#L67-L84

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis
variable {σ X : Type} [Fintype X] [DecidableEq X]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.det_unit (m : X → σ →₀ ℕ) (hm : Function.Injective m) (F : X → MvPolynomial σ ℤ)
    (hF : ∀ x, ∀ d ∈ (F x).support, d ∈ Set.range m)
    (hp : ∀ p : ℕ, ∀ _ : Fact p.Prime,
      LinearIndependent (ZMod p) fun x => MvPolynomial.map (Int.castRingHom (ZMod p)) (F x)) :
    IsUnit (cmat m F).det := by sorry
