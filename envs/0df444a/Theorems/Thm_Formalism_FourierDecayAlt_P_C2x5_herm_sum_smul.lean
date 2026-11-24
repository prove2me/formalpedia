-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_herm_sum_smul
-- name    : Formalism.FourierDecayAlt.P.C2x5.herm_sum_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:32:29.177138+00:00
-- url     : https://prove2.me/theorems/dac9560e-daf7-4ee7-8289-5dfff3b3a52a
-- title:
--   C2x5: herm sum smul
-- statement:
--   The C2x5 construction uses the herm sum smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean#L12-L15

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
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
open Formalism.FourierDecayAlt.P.C2x5
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x5.herm_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin n) (Fin n) ℂ) (x : ι → ℂ)
    (v : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ c, x c • v c) w = ∑ c, x c * herm H (v c) w := by sorry
