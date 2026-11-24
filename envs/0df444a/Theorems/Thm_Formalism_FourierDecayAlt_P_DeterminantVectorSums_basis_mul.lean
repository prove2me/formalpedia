-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_basis_mul
-- name    : Formalism.FourierDecayAlt.P.DeterminantVectorSums.basis_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:32:08.529507+00:00
-- url     : https://prove2.me/theorems/e27881c3-b95a-4fca-bb99-cd12aa6da9b8
-- title:
--   Determinant Vector Sums: basis mul
-- statement:
--   The Determinant Vector Sums construction uses the basis mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L168-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StarSumLemmas.lean#L168-L173

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem Formalism.FourierDecayAlt.P.DeterminantVectorSums.basis_mul {n : ℕ} (r : Fin n → ℂ) (i : Fin n) :
    (X - C (r i)) * Lagrange.basis univ r i =
      C (∏ j ∈ univ.erase i, (r i - r j)⁻¹) * ∏ j, (X - C (r j)) := by sorry
