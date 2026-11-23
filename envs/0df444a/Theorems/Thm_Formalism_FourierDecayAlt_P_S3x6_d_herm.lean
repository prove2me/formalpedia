-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_herm
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:59.224375+00:00
-- url     : https://prove2.me/theorems/493a729c-3d85-4543-986f-4783fcd9c9d0
-- title:
--   S3x6: d herm
-- statement:
--   The S3x6 construction uses the d herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L754-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L754-L765

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_herm {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hi : Inv σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (hJh : fconj q J = J) : Herm (hJ σ J) := by sorry
