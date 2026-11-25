-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_herm_Zv
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_Zv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:33.785043+00:00
-- url     : https://prove2.me/theorems/8b3a335e-76b9-503c-b549-1a84faef762e
-- title:
--   Sign Antidiagonal: herm Zv
-- statement:
--   The Sign Antidiagonal construction uses the herm Zv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L157-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangularFactorMiddleRow.lean#L157-L170

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_Zv (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hiso : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b b' : Fin j) :
    herm (Hpk k r) (Zv k r j hj y b') (Zv k r j hj y b) = 0 := by sorry
