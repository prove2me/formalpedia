-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_dp2
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.dp2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:47.513059+00:00
-- url     : https://prove2.me/theorems/103d1478-5019-433d-a607-4a1760419169
-- title:
--   Sign Antidiagonal: dp2
-- statement:
--   The Sign Antidiagonal construction uses the dp2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean#L45-L47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
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
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.dp2 (hp : p.val < r) (hq1 : r ≤ q.val) (hq2 : q.val ≤ r + k) :
    dpsiP k r z' p q = if p.val + 1 = r then z' q else 0 := by sorry
