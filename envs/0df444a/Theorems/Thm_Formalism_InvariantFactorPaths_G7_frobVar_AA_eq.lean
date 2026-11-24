-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_AA_eq
-- name    : Formalism.InvariantFactorPaths.G7.frobVar_AA_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:30:11.348014+00:00
-- url     : https://prove2.me/theorems/bf7c4c0c-201e-4ada-a429-1d67dc9d7a31
-- title:
--   G7: frob Var AA eq
-- statement:
--   The G7 construction uses the frob Var AA eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L307-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L307-L353

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem Formalism.InvariantFactorPaths.G7.frobVar_AA_eq (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {x y : Fin 2}
    (hxy : x ≠ y) :
    frobVar p (AA K p x y) =
      MvPowerSeries.C (p : K) * (at1 x (g0F K p) * at1 y (lgF K p) - AA K p y x) := by sorry
