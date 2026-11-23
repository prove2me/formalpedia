-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_li_of_rank
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_li_of_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:09.000412+00:00
-- url     : https://prove2.me/theorems/27f3467e-d36b-4067-ba29-76f9461a24b4
-- title:
--   S3x6: d li of rank
-- statement:
--   The S3x6 construction uses the d li of rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L781-L787
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L781-L787

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_li_of_rank {n a : ℕ} (X : Matrix (Fin n) (Fin a) K) (hX : X.rank = a) :
    LinearIndependent K (fun (i : Fin a) (k : Fin n) => X k i) := by sorry
