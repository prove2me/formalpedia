-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_h_series
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_h_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:37.189817+00:00
-- url     : https://prove2.me/theorems/0f474ab1-573f-4702-97fb-dda7c97a929f
-- title:
--   Coboundary Series: partial coboundary h series
-- statement:
--   The Coboundary Series construction uses the partial coboundary h series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L103-L109

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
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
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_h_series {p : ℕ} (σ : K →+* K) {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (hl : cob F (lgF K p) = 0) (G : MvPowerSeries (Fin 2) K) (γ γ' : K) :
    d1 F (Hser p σ G γ γ') =
      d1 F (DeS p σ G) - C γ * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by sorry
