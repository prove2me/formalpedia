-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_add
-- name    : Formalism.DworkPowerSeriesWeights.dot_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:59.420864+00:00
-- url     : https://prove2.me/theorems/a3e451a3-e6cb-43dc-aa74-5dbc18c60ce8
-- title:
--   Dwork Power Series Weights: dot add
-- statement:
--   The Dwork Power Series Weights construction uses the dot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L18-L21

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [NormedField K] {ι : Type v}

theorem Formalism.DworkPowerSeriesWeights.dot_add (m n : ι →₀ ℕ) (r : ι → ℝ) : dot (m + n) r = dot m r + dot n r := by sorry
