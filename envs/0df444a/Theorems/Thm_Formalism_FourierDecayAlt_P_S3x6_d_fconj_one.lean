-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_one
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_fconj_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:33.00959+00:00
-- url     : https://prove2.me/theorems/80904a55-82d8-4641-9799-07dd2a9106be
-- title:
--   S3x6: d fconj one
-- statement:
--   The S3x6 construction uses the d fconj one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L750-L752
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L750-L752

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_fconj_one {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α : Type} [DecidableEq α] :
    fconj q (1 : Matrix α α K) = 1 := by sorry
