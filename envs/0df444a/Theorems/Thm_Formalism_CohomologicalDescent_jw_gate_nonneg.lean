-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_jw_gate_nonneg
-- name    : Formalism.CohomologicalDescent.jw_gate_nonneg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:54:54.624001+00:00
-- url     : https://prove2.me/theorems/25daa40f-619e-4710-beb6-8cd8b19ed30c
-- title:
--   Cohomological Descent: jw gate nonneg
-- statement:
--   The Cohomological Descent construction uses the jw gate nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/JointCorollaryFiveBound.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/JointCorollaryFiveBound.lean#L27-L33

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_JointCW5
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem Formalism.CohomologicalDescent.jw_gate_nonneg {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) :
    (0 : ℝ) ≤ (if ((D.d0 τ l : ℕ) : ℤ) < Cor.DB D τ then
        min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ)) else 0) := by sorry
