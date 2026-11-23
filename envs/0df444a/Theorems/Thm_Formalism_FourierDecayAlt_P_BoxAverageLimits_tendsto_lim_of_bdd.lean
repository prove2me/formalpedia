-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_tendsto_lim_of_bdd
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.tendsto_lim_of_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:07.073908+00:00
-- url     : https://prove2.me/theorems/c302f1c8-972d-45ce-a47c-f942ae57f3a5
-- title:
--   Box Average Limits: tendsto lim of bdd
-- statement:
--   The Box Average Limits construction uses the tendsto lim of bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L44-L50

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.tendsto_lim_of_bdd (u : ℕ → ℂ) (B : ℝ) (hu : ∀ n, ‖u n‖ ≤ B) :
    Tendsto u (hyperfilter ℕ : Filter ℕ) (𝓝 (limUnder (hyperfilter ℕ : Filter ℕ) u)) := by sorry
