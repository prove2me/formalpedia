-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_mvExp
-- name    : Formalism.InvariantFactorPaths.G7.coeff_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:31.927875+00:00
-- url     : https://prove2.me/theorems/afdbf84e-5ae8-4f20-99f4-d483155e3749
-- title:
--   G7: coeff mv Exp
-- statement:
--   The G7 construction uses the coeff mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L90-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L90-L107

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

theorem Formalism.InvariantFactorPaths.G7.coeff_mvExp {K ι : Type} [NormedField K] [CharZero K] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (mvExp f) =
      ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) := by sorry
