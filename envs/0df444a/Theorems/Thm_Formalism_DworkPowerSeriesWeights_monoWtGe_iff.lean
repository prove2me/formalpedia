-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
-- name    : Formalism.DworkPowerSeriesWeights.monoWtGe_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:40.912834+00:00
-- url     : https://prove2.me/theorems/11f9191b-d33d-4bc8-8365-c3114b2513dd
-- title:
--   Dwork Power Series Weights: mono Wt Ge iff
-- statement:
--   The Dwork Power Series Weights construction uses the mono Wt Ge iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/SubstitutionWeightBound.lean#L15-L16

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

theorem Formalism.DworkPowerSeriesWeights.monoWtGe_iff {pi : ℝ} {r : ι → ℝ} {wt : ℝ} {n : ι →₀ ℕ} {c : K} :
    MonoWtGe pi r wt n c ↔ ‖c‖ ≤ pi ^ (wt - dot n r) := by sorry
