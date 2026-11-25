-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_hermitian_insertion_vector_orthogonal
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.hermitian_insertion_vector_orthogonal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:04:45.905919+00:00
-- url     : https://prove2.me/theorems/d604234e-57a2-45fd-a7d2-45eef5c48d26
-- title:
--   Sign Antidiagonal: hermitian insertion vector orthogonal
-- statement:
--   The Sign Antidiagonal construction uses the hermitian insertion vector orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L82-L89

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.hermitian_insertion_vector_orthogonal (z' : Fin (2 * (m + 1) + k + 1) → ℂ) (hz : inWb k (m + 1) z') :
    herm (Hpk k (m + 1)) z' (ViF m i Vc) = 0 := by sorry
