-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_basis_mul
-- name    : Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.basis_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:41.608012+00:00
-- url     : https://prove2.me/theorems/cffe46c5-d52c-4294-aae1-f0c4dcd0c5d5
-- title:
--   Capelli Abstract Character: basis mul
-- statement:
--   The Capelli Abstract Character construction uses the basis mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L311-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CapelliAbstractCharacter.lean#L311-L324

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.basis_mul {N : ℕ} (m : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    ∃ w : ℂ, ((Polynomial.X : ℂ[X]) + C (m i)) * Lagrange.basis Finset.univ (fun j => -m j) i =
      C w * ∏ j, ((Polynomial.X : ℂ[X]) + C (m j)) := by sorry
