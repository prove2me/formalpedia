-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_gAbs_add_le_max
-- name    : Formalism.DworkPowerSeriesWeights.gAbs_add_le_max
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:35.565594+00:00
-- url     : https://prove2.me/theorems/25304e87-3a9b-4d9a-87cd-b25b86e4ed45
-- title:
--   Dwork Power Series Weights: g Abs add le max
-- statement:
--   The Dwork Power Series Weights construction uses the g Abs add le max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L187-L190

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

theorem Formalism.DworkPowerSeriesWeights.gAbs_add_le_max (x y : GK F σ) : gAbs F σ (x + y) ≤ max (gAbs F σ x) (gAbs F σ y) := by sorry
