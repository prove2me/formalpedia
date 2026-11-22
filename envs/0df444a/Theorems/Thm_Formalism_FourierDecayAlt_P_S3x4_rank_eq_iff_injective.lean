-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_rank_eq_iff_injective
-- name    : Formalism.FourierDecayAlt.P.S3x4.rank_eq_iff_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:08:23.194012+00:00
-- url     : https://prove2.me/theorems/52d187e2-0266-45d8-a50d-bb6b9a8d369b
-- title:
--   S3x4: rank eq iff injective
-- statement:
--   The S3x4 construction uses the rank eq iff injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L243-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L243-L250

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
open Matrix Finset Module
variable {K : Type} [Field K]

theorem Formalism.FourierDecayAlt.P.S3x4.rank_eq_iff_injective {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) :
    X.rank = a ↔ Function.Injective (Matrix.toLin' X) := by sorry
