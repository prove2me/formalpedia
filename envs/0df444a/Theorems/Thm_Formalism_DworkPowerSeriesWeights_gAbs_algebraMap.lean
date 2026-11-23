-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_algebraMap
-- name    : Formalism.DworkPowerSeriesWeights.gAbs_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:50.287216+00:00
-- url     : https://prove2.me/theorems/b382f7fa-238c-4003-a2f2-0c7bf55f721f
-- title:
--   Dwork Power Series Weights: g Abs algebra Map
-- statement:
--   The Dwork Power Series Weights construction uses the g Abs algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L192-L193

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {F : Type} [NormedField F] {σ : Type}
variable [IsUltrametricDist F]

theorem Formalism.DworkPowerSeriesWeights.gAbs_algebraMap (P : MvPolynomial σ F) : gAbs F σ (algebraMap _ (GK F σ) P) = gN P := by sorry
