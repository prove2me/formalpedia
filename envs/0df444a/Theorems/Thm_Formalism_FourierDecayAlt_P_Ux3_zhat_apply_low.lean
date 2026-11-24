-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_zhat_apply_low
-- name    : Formalism.FourierDecayAlt.P.Ux3.zhat_apply_low
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:40.089839+00:00
-- url     : https://prove2.me/theorems/0530971e-72cb-49bb-8a8a-f523228741f1
-- title:
--   Ux3: zhat apply low
-- statement:
--   The Ux3 construction uses the zhat apply low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L126-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L126-L137

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

theorem Formalism.FourierDecayAlt.P.Ux3.zhat_apply_low (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin (r + 1)) (ha : a.val < r) (hb : b.val < r) :
    Zhat k r z z' g a b = g ⟨2 * r + k - a.val, by omega⟩ ⟨b.val, by omega⟩ := by sorry
