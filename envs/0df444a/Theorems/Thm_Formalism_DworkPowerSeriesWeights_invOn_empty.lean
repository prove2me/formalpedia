-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_invOn_empty
-- name    : Formalism.DworkPowerSeriesWeights.invOn_empty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:36.810827+00:00
-- url     : https://prove2.me/theorems/5830cbd4-1e75-4e0b-9891-22503ba0d2ea
-- title:
--   Dwork Power Series Weights: inv On empty
-- statement:
--   The Dwork Power Series Weights construction uses the inv On empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L221-L228

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
variable {R : Type u} [CommRing R]

theorem Formalism.DworkPowerSeriesWeights.invOn_empty : invOn (∅ : Finset (Fin n)) = {1} := by sorry
