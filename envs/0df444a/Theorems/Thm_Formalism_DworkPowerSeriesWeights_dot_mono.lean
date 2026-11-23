-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_mono
-- name    : Formalism.DworkPowerSeriesWeights.dot_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:55.930149+00:00
-- url     : https://prove2.me/theorems/6deb874c-3ac3-4025-bc77-e3ce39336851
-- title:
--   Dwork Power Series Weights: dot mono
-- statement:
--   The Dwork Power Series Weights construction uses the dot mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L25-L27

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

theorem Formalism.DworkPowerSeriesWeights.dot_mono (n : ι →₀ ℕ) {r r' : ι → ℝ} (h : ∀ i, r i ≤ r' i) : dot n r ≤ dot n r' := by sorry
