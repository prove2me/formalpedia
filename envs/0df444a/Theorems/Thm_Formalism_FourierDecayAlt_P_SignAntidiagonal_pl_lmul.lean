-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_lmul
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_lmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:59.493806+00:00
-- url     : https://prove2.me/theorems/13af0849-89b4-43ce-bd68-be8990fd80d0
-- title:
--   Sign Antidiagonal: pl lmul
-- statement:
--   The Sign Antidiagonal construction uses the pl lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L39-L44

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_lmul {t : ℕ} {f : ℂ → A} (c : A) (hf : PolyLe t f) : PolyLe t (fun u => c * f u) := by sorry
