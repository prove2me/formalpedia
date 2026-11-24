-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_wt_step
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.wt_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:23.088628+00:00
-- url     : https://prove2.me/theorems/a9740aeb-20fd-499c-8a7d-73a08994f155
-- title:
--   A1hw: wt step
-- statement:
--   The A1hw construction uses the wt step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L21-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathProductHighestWeight.lean#L21-L46

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1hw.wt_step {σ R : Type*} [CommRing R] {n : ℕ} (w : σ → ℤ) (up : Bool) (m : Fin n) (s : ℤ)
    (Kf : Form (MvPolynomial σ R) n) (Xv : Fin n → MvPolynomial σ R)
    (hK : ∀ J, IsWeightedHomogeneous w (Kf J) (if m ∈ J then s else 0))
    (hX : ∀ m', IsWeightedHomogeneous w (Xv m') (if m' = m then (if up then s else -s) else 0))
    (J : Finset (Fin n)) : IsWeightedHomogeneous w (stepF up Kf Xv J) (if m ∈ J then s else 0) := by sorry
