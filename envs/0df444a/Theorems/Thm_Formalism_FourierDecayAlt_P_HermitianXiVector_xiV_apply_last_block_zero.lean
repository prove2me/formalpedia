-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianXiVector_xiV_apply_last_block_zero
-- name    : Formalism.FourierDecayAlt.P.HermitianXiVector.xiV_apply_last_block_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:44:57.233803+00:00
-- url     : https://prove2.me/theorems/8acb223e-a29b-4c98-8c64-ac1cc4359657
-- title:
--   Hermitian Xi Vector: xi V apply last block zero
-- statement:
--   The Hermitian Xi Vector construction uses the xi V apply last block zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianXiVector.lean#L72-L77

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

theorem Formalism.FourierDecayAlt.P.HermitianXiVector.xiV_apply_last_block_zero (ξ : Fin r → ℂ) : ∀ i : Fin (2 * r + k + 1), r + k < i.val → C2.xiV k r ξ i = 0 := by sorry
