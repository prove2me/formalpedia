-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_inv_le_exp
-- name    : Formalism.FourierDecayAlt.P.S3x5.densityProduct_inv_le_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:19.751565+00:00
-- url     : https://prove2.me/theorems/891f2bb4-79e4-49c3-9f4c-77242a9ea27d
-- title:
--   S3x5: density Product inv le exp
-- statement:
--   The S3x5 construction uses the density Product inv le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L104-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L104-L119

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x5.densityProduct_inv_le_exp (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    (densP η q lo hi)⁻¹ ≤ Real.exp (∑ i ∈ Finset.Icc lo hi, 2 * (q : ℝ) ^ (-i)) := by sorry
