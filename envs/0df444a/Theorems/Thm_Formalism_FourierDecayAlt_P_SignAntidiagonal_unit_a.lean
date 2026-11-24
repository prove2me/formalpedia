-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_unit_a
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.unit_a
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:41.70793+00:00
-- url     : https://prove2.me/theorems/1f829604-a3c9-4c31-a301-91b51eeec53a
-- title:
--   Sign Antidiagonal: unit a
-- statement:
--   The Sign Antidiagonal construction uses the unit a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DpsiIsDerivation.lean#L66-L81

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.unit_a (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (a : Fin r) (ha : a.val + 1 < r) :
    X (esI k r ⟨a.val + 1, ha⟩) (esI k r a) = -star (X (eI k r a) (eI k r ⟨a.val + 1, ha⟩)) := by sorry
