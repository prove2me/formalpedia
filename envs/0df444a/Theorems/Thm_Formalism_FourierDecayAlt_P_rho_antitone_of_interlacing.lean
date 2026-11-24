-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_rho_antitone_of_interlacing
-- name    : Formalism.FourierDecayAlt.P.rho_antitone_of_interlacing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:39:39.132476+00:00
-- url     : https://prove2.me/theorems/d50899c1-7adf-4054-9c12-e2e308df4025
-- title:
--   P: rho antitone of interlacing
-- statement:
--   The P construction uses the rho antitone of interlacing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RhoAntitoneOfInterlacing.lean#L28-L37

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.rho_antitone_of_interlacing {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by sorry
