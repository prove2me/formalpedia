-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_not_range_rev
-- name    : Formalism.FourierDecayAlt.P.S3x7.not_range_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:48.162079+00:00
-- url     : https://prove2.me/theorems/d5f87711-694d-4afd-a762-306e9f0dea33
-- title:
--   S3x7: not range rev
-- statement:
--   The S3x7 construction uses the not range rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L53-L59

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x7.not_range_rev {l r : ℕ} (hl : l ≤ r) {k : Fin r}
    (hk : k ∉ Set.range (fun i : Fin l => (Fin.castLE hl i).rev)) : k.val + l < r := by sorry
