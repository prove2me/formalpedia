-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_left_alt
-- name    : Formalism.FourierDecayAlt.P.S3x6.form_sum_left_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:35.56733+00:00
-- url     : https://prove2.me/theorems/7dad1aef-e3e3-473e-aebd-9470e08e7473
-- title:
--   S3x6: form sum left alt
-- statement:
--   The S3x6 construction uses the form sum left alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L212-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L212-L214

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

theorem Formalism.FourierDecayAlt.P.S3x6.form_sum_left_alt (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (u : V) (c : ι → K)
    (x : ι → V) : h (∑ j, c j • x j) u = ∑ j, σ (c j) * h (x j) u := by sorry
