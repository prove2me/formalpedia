-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_tri_integral
-- name    : Formalism.DworkPowerSeriesWeights.sat_tri_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:44.108366+00:00
-- url     : https://prove2.me/theorems/a0a68531-6e8a-48af-8374-e94f9a220f2b
-- title:
--   Dwork Power Series Weights: sat tri integral
-- statement:
--   The Dwork Power Series Weights construction uses the sat tri integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SlopeBoundSaturation.lean#L13-L31

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
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
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility

theorem Formalism.DworkPowerSeriesWeights.sat_tri_integral {K ι : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [PartialOrder ι]
    (T : ι → ι → K) (hT : ∀ i j, ‖T i j‖ ≤ 1) (hd : ∀ i, T i i = 1) (h0 : ∀ i j, ¬ i ≤ j → T i j = 0)
    (c : ι → K) (hc : ∀ i, ‖∑ j, c j * T i j‖ ≤ 1) : ∀ i, ‖c i‖ ≤ 1 := by sorry
