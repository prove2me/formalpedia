-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_card_slab
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.card_slab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:32.60279+00:00
-- url     : https://prove2.me/theorems/b9da311b-8de5-4ded-9537-a5cb7551d925
-- title:
--   Box Average Limits: card slab
-- statement:
--   The Box Average Limits construction uses the card slab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L102-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L102-L113

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.card_slab (R : ℕ) (j : ι) (a : ℕ) :
    (Fintype.piFinset (Function.update (fun _ : ι => range R) j {a})).card =
      R ^ (Fintype.card ι - 1) := by sorry
