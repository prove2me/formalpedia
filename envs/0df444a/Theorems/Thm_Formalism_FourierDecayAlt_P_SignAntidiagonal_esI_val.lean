-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_esI_val
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.esI_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:24.829019+00:00
-- url     : https://prove2.me/theorems/8fdf73e8-3a04-4e7d-8bf4-13db294e5026
-- title:
--   Sign Antidiagonal: es I val
-- statement:
--   The Sign Antidiagonal construction uses the es I val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L104-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L104-L104

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.esI_val (b : Fin r) : (esI k r b).val = 2 * r + k - b.val := by sorry
