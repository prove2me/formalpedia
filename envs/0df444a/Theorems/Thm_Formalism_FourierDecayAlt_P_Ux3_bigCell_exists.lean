-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCell_exists
-- name    : Formalism.FourierDecayAlt.P.Ux3.bigCell_exists
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:22:19.985805+00:00
-- url     : https://prove2.me/theorems/9553f7de-178d-405c-816b-4f7148528f9a
-- title:
--   Ux3: big Cell exists
-- statement:
--   The Ux3 construction uses the big Cell exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L636-L774
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L636-L774

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

theorem Formalism.FourierDecayAlt.P.Ux3.bigCell_exists (g : B.Mat k (j + ρ)) (hg : g ∈ B.GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    ∃ (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ), Z.det ≠ 0 ∧ γ ∈ B.GV k ρ ∧
      g = (Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x' := by sorry
