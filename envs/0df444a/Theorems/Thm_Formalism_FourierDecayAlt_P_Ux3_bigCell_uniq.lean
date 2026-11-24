-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCell_uniq
-- name    : Formalism.FourierDecayAlt.P.Ux3.bigCell_uniq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:02.010079+00:00
-- url     : https://prove2.me/theorems/79490258-77b9-4b28-a529-38ed60c914b2
-- title:
--   Ux3: big Cell uniq
-- statement:
--   The Ux3 construction uses the big Cell uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L513-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L513-L566

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux3.bigCell_uniq (x1 x1' x2 x2' : RC k j ρ) (Z1 Z2 : Matrix (Fin j) (Fin j) ℂ) (γ1 γ2 : B.Mat k ρ)
    (hZ1 : Z1.det ≠ 0) (hZ2 : Z2.det ≠ 0) (hγ2 : γ2 ∈ B.GV k ρ)
    (h : (Rn k j ρ x1)⁻¹ * mMap k j ρ Z1 γ1 * Rn k j ρ x1' = (Rn k j ρ x2)⁻¹ * mMap k j ρ Z2 γ2 * Rn k j ρ x2') :
    x1 = x2 ∧ x1' = x2' ∧ Z1 = Z2 ∧ γ1 = γ2 := by sorry
