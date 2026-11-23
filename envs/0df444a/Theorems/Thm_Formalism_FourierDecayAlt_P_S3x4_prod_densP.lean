-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_prod_densP
-- name    : Formalism.FourierDecayAlt.P.S3x4.prod_densP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:17.775324+00:00
-- url     : https://prove2.me/theorems/e1a1ac81-6b4d-4b0b-906f-1e07a207ed45
-- title:
--   S3x4: prod dens P
-- statement:
--   The S3x4 construction uses the prod dens P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L399-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L399-L418

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x4.prod_densP (q : ℕ) (hq : 0 < q) (m : ℕ) (hi : ℤ) (hm : (m : ℤ) ≤ hi) (k : ℕ) (hk : k ≤ m) :
    ((∏ j ∈ range k, (q ^ m - q ^ j) : ℕ) : ℝ) * densP 1 q ((m : ℤ) + 1) hi =
      (q : ℝ) ^ (m * k) * densP 1 q ((m : ℤ) - k + 1) hi := by sorry
