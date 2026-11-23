-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_mul
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_fconj_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:26.452343+00:00
-- url     : https://prove2.me/theorems/2b4909c7-a956-47a6-b9f7-561701cc30aa
-- title:
--   S3x6: d fconj mul
-- statement:
--   The S3x6 construction uses the d fconj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L746-L748
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L746-L748

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_fconj_mul {q : ℕ} (hσ : ∀ x, σ x = x ^ q) {α β γ : Type} [Fintype β] (X : Matrix α β K)
    (Y : Matrix β γ K) : fconj q (X * Y) = fconj q Y * fconj q X := by sorry
