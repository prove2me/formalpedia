-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_mono_const
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_mono_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:05.82789+00:00
-- url     : https://prove2.me/theorems/a2141b31-9b22-4d21-be9f-6dbc92614456
-- title:
--   Sign Antidiagonal: pl mono const
-- statement:
--   The Sign Antidiagonal construction uses the pl mono const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L68-L71

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
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
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_mono_const (t : ℕ) (x : A) : PolyLe (t + 1) (fun u => algebraMap ℂ A (u ^ t) * x) := by sorry
