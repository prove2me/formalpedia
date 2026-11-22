-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_hJ_apply
-- name    : Formalism.FourierDecayAlt.P.S3x6.hJ_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:04.066953+00:00
-- url     : https://prove2.me/theorems/307062b8-99bd-4490-870f-68e12ef72e28
-- title:
--   S3x6: h J apply
-- statement:
--   The S3x6 construction uses the h J apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L726-L732
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L726-L732

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.S3x6.hJ_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hJ σ J u v = ∑ i, ∑ j, σ (u i) * J i j * v j := by sorry
