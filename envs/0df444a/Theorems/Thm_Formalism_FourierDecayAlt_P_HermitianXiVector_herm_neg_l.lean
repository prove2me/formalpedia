-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_herm_neg_l
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.herm_neg_l
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:02:10.191126+00:00
-- url     : https://prove2.me/theorems/9845d08b-d32b-4f47-94b0-1bf58205ca4c
-- title:
--   Hermitian Xi Vector: herm neg l
-- statement:
--   The Hermitian Xi Vector construction uses the herm neg l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L31-L33

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
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
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.herm_neg_l {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a w : Fin n → ℂ) :
    herm H (-a) w = -herm H a w := by sorry
