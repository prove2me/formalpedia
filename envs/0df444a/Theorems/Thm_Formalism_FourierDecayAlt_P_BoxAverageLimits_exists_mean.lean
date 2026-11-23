-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_exists_mean
-- name    : Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_mean
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:47.174202+00:00
-- url     : https://prove2.me/theorems/779a92b4-5553-4368-accb-191233e75a76
-- title:
--   Box Average Limits: exists mean
-- statement:
--   The Box Average Limits construction uses the exists mean property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L282-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AverageOne.lean#L282-L322

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

theorem Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_mean (e : ι → Λ) (he : AddSubgroup.closure (Set.range e) = ⊤) (c : ℕ → Λ) :
    IsMean (LIMf e c) ∧ ∀ g, Bdd g →
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ ≤ ε) → LIMf e c g = 0 := by sorry
