-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_triangular_factor_middle_row
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.triangular_factor_middle_row
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:47.169878+00:00
-- url     : https://prove2.me/theorems/16887c73-e0b3-4ad3-a622-07372bd3fd26
-- title:
--   Sign Antidiagonal: triangular factor middle row
-- statement:
--   The Sign Antidiagonal construction uses the triangular factor middle row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L89-L91

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.triangular_factor_middle_row (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
    (hp : r ≤ p.val ∧ p.val ≤ r + k) : Tn k r j hj y p q = Cf k r j hj y p q := by sorry
