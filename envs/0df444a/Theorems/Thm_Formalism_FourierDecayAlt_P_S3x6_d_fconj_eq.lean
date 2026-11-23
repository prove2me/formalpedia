-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_eq
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_fconj_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:43.252386+00:00
-- url     : https://prove2.me/theorems/3a798647-1832-4c1d-94d8-a2a0abbeed72
-- title:
--   S3x6: d fconj eq
-- statement:
--   The S3x6 construction uses the d fconj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L741-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L741-L744

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_fconj_eq {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β : Type} (X : Matrix α β K) :
    fconj q X = (X.map σ)ᵀ := by sorry
