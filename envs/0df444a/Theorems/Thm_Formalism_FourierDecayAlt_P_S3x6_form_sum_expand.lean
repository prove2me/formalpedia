-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_expand
-- name    : Formalism.FourierDecayAlt.P.S3x6.form_sum_expand
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:15.55456+00:00
-- url     : https://prove2.me/theorems/21766615-84d1-4857-89c4-61d41dd1260f
-- title:
--   S3x6: form sum expand
-- statement:
--   The S3x6 construction uses the form sum expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L269-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L269-L273

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
variable {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.FourierDecayAlt.P.S3x6.form_sum_expand (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] (b : κ → V) (c d : κ → K) :
    h (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, σ (c i) * (d j * h (b i) (b j)) := by sorry
