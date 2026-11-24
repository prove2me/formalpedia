-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_part_ne_zero
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.part_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:27.373047+00:00
-- url     : https://prove2.me/theorems/039438ac-e019-4de0-8c26-4536f0843797
-- title:
--   Gelfand Tsetlin Bases: part ne zero
-- statement:
--   The Gelfand Tsetlin Bases construction uses the part ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L333-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L333-L350

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
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
variable {ι ζ : Type*} {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.part_ne_zero {σ L : Type*} [CommRing L] (H : MvPolynomial σ L) (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    (∑ e ∈ H.support.filter p, monomial e (coeff e H)) ≠ 0 ↔ ∃ e ∈ H.support, p e := by sorry
