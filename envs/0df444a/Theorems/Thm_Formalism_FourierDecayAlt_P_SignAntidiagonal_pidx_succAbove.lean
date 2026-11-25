-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pidx_succAbove
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.pidx_succAbove
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:31:57.003438+00:00
-- url     : https://prove2.me/theorems/8cd90fab-4548-404f-a44c-9f1ea47fa6be
-- title:
--   Sign Antidiagonal: pidx succ Above
-- statement:
--   The Sign Antidiagonal construction uses the pidx succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L22-L24

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
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.pidx_succAbove (m : ℕ) (i : Fin (m + 1)) (b : Fin m) (h : (i.succAbove b).val < m + 1 ∧ (i.succAbove b).val ≠ i.val) :
    pidx m i (i.succAbove b).val h = b := by sorry
