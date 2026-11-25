-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_succAbove_pidx
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.succAbove_pidx
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:31:36.12056+00:00
-- url     : https://prove2.me/theorems/552889f4-32c6-5d49-8d59-b34fce107570
-- title:
--   Sign Antidiagonal: succ Above pidx
-- statement:
--   The Sign Antidiagonal construction uses the succ Above pidx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L18-L20

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.succAbove_pidx (m : ℕ) (i : Fin (m + 1)) (c : ℕ) (h : c < m + 1 ∧ c ≠ i.val) :
    (i.succAbove (pidx m i c h)).val = c := by sorry
