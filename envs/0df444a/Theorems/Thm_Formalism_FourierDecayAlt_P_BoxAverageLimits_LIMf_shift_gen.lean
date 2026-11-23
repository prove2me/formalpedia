-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_LIMf_shift_gen
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.LIMf_shift_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:45.5408+00:00
-- url     : https://prove2.me/theorems/0277b537-269d-4c3a-baaa-1179cafc15fc
-- title:
--   Box Average Limits: LIMf shift gen
-- statement:
--   The Box Average Limits construction uses the LIMf shift gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L228-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L228-L242

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.LIMf_shift_gen (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (hg : Bdd g) (j : ι) :
    LIMf e c (fun x => g (x + e j)) = LIMf e c g := by sorry
