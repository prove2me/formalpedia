-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:31.667829+00:00
-- url     : https://prove2.me/theorems/42b6741b-7d25-42c8-a647-183b66bc5bdc
-- title:
--   Sign Antidiagonal: ps val
-- statement:
--   The Sign Antidiagonal construction uses the ps val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L89-L89

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val (k r p : ℕ) : (ps k r p).val = 2 * r + k - p := by sorry

attribute [defeq] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
