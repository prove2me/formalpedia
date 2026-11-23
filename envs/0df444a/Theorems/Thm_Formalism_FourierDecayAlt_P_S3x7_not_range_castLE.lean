-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_not_range_castLE
-- name    : Formalism.FourierDecayAlt.P.S3x7.not_range_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:34.005809+00:00
-- url     : https://prove2.me/theorems/e9279281-f147-4c90-9500-4c6ab474403a
-- title:
--   S3x7: not range cast LE
-- statement:
--   The S3x7 construction uses the not range cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L48-L51

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

theorem Formalism.FourierDecayAlt.P.S3x7.not_range_castLE {l r : ℕ} (hl : l ≤ r) {k : Fin r} (hk : k ∉ Set.range (Fin.castLE hl)) :
    l ≤ k.val := by sorry
