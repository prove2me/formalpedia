-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pl_sum
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:53:29.94362+00:00
-- url     : https://prove2.me/theorems/f722c987-ccb0-4071-bd5e-83284824b7e1
-- title:
--   Sign Antidiagonal: pl sum
-- statement:
--   The Sign Antidiagonal construction uses the pl sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PlMonoConst.lean#L30-L37

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ → A) (hf : ∀ i ∈ s, PolyLe t (f i)) :
    PolyLe t (fun u => ∑ i ∈ s, f i u) := by sorry
