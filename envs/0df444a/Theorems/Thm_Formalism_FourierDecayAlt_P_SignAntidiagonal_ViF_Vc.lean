-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ViF_Vc
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_Vc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:32:39.014803+00:00
-- url     : https://prove2.me/theorems/b29386b4-c921-54b9-ae19-aaed0a558005
-- title:
--   Sign Antidiagonal: Vi F Vc
-- statement:
--   The Sign Antidiagonal construction uses the Vi F Vc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L99-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L99-L133

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.ViF_Vc (hVs : ∀ (b : Fin m) (q : Fin (2 * (m + 1) + k + 1)), m + 1 + k < q.val →
      Vc b q = if (NFOne.sg k (m + 1) q).val = (i.succAbove b).val then 1 else 0) (c' : Fin m) :
    herm (Hpk k (m + 1)) (ViF m i Vc) (Vc c') = 0 := by sorry
