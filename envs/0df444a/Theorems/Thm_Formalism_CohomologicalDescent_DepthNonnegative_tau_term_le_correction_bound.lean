-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tau_term_le_correction_bound
-- name    : Formalism.CohomologicalDescent.DepthNonnegative.tau_term_le_correction_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:58.102096+00:00
-- url     : https://prove2.me/theorems/25bdfbf6-447b-44ef-8961-ae2d71e3eba1
-- title:
--   Depth Nonnegative: tau term le correction bound
-- statement:
--   The Depth Nonnegative construction uses the tau term le correction bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L247-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DepthNonnegative.lean#L247-L263

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem Formalism.CohomologicalDescent.DepthNonnegative.tau_term_le_correction_bound {ι : Type} [DecidableEq ι] (D : Data ι) (hP : D.Params) (l : ℕ) (hl : l.Prime) (τ : ι) :
    ((cTau D.T2 (fun τ => D.ex τ l) (fun τ =>
        ⌊cPrime l D.k (D.j τ) D.t (D.q τ) D.h (D.ecl τ l) (D.xlo τ) (D.xhi τ) (D.maxB τ)
          (D.depth τ l : ℝ)⌋₊) τ : ℕ) : ℝ) ≤
      (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (Cor.coefficientBoundTau D τ l) else (D.ex τ l : ℝ)) := by sorry
