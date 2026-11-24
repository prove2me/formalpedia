-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sums_harmonic_real
-- name    : Formalism.CohomologicalDescent.sums_harmonic_real
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:50.41039+00:00
-- url     : https://prove2.me/theorems/64f40dcc-2cf6-4785-a218-846d4ca0e849
-- title:
--   Cohomological Descent: sums harmonic real
-- statement:
--   The Cohomological Descent construction uses the sums harmonic real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
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
open Classical

theorem Formalism.CohomologicalDescent.sums_harmonic_real (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log n := by sorry
