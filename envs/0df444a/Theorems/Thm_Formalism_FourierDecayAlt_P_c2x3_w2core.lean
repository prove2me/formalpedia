-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_w2core
-- name    : Formalism.FourierDecayAlt.P.c2x3_w2core
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:37:51.871113+00:00
-- url     : https://prove2.me/theorems/395ad40e-17c2-4235-a113-46b28a39cf2a
-- title:
--   P: c2x3 w2core
-- statement:
--   The P construction uses the c2x3 w2core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L19-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L19-L40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x3_w2core (y : ℕ → ℝ) (hy : ∀ i, 0 < y i) (h0 : y 0 = 1) (K : ℕ) : ∀ r : ℕ,
    ∏ l ∈ Finset.range r, (y (l + 1) / y l) ^ (4 * (r - l) + K) =
      y r ^ K * ∏ l ∈ Finset.range r, y (l + 1) ^ 4 := by sorry
