-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_unique
-- name    : Formalism.CohomologicalDescent.LD.ld_sym_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:49:08.386315+00:00
-- url     : https://prove2.me/theorems/481f77b2-a671-425b-8640-375f706f9685
-- title:
--   LD: ld sym unique
-- statement:
--   The LD construction uses the ld sym unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L899-L954
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L899-L954

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.ld_sym_unique (q w : ℕ) (μ : Fin (1 + q) → ℕ) (x : MvPolynomial (Fin (1 + q) × Fin (1 + q)) ℤ)
    (hx : x ∈ nablaWt (1 + q) (blockWt 1 q w fun _ => 0) μ) (hne : x ≠ 0) :
    ∑ a, μ a = w ∧ ∃ c : ℤ, x = c • ∏ a, X (a, ldZ q) ^ μ a := by sorry
