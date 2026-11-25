-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_rmul
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_rmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:35.65382+00:00
-- url     : https://prove2.me/theorems/cc228f67-5bd4-5669-9866-34ea464f42c5
-- title:
--   Sign Antidiagonal: pl rmul
-- statement:
--   The Sign Antidiagonal construction uses the pl rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L46-L51

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_rmul {t : ℕ} {f : ℂ → A} (e : A) (hf : PolyLe t f) : PolyLe t (fun u => f u * e) := by sorry
