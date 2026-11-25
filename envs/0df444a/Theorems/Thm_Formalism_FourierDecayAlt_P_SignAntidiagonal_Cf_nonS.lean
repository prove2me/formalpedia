-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_Cf_nonS
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.Cf_nonS
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:49.270557+00:00
-- url     : https://prove2.me/theorems/3f06f7fa-1113-5077-a9fa-dcbdacd493ad
-- title:
--   Sign Antidiagonal: Cf non S
-- statement:
--   The Sign Antidiagonal construction uses the Cf non S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L85-L87

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
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
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.Cf_nonS (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (l q : Fin (2 * r + k + 1))
    (hq : ¬ r + k < q.val) : Cf k r j hj y l q = 0 := by sorry
