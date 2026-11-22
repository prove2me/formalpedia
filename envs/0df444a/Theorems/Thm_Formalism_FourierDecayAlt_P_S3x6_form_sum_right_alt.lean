-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt
-- name    : Formalism.FourierDecayAlt.P.S3x6.form_sum_right_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:27.247933+00:00
-- url     : https://prove2.me/theorems/db6ba2ca-69b1-4ca3-8b7c-715f1cd888df
-- title:
--   S3x6: form sum right alt
-- statement:
--   The S3x6 construction uses the form sum right alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L208-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L208-L210

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

theorem Formalism.FourierDecayAlt.P.S3x6.form_sum_right_alt (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [Fintype ι] (u : V) (c : ι → K)
    (x : ι → V) : h u (∑ j, c j • x j) = ∑ j, c j * h u (x j) := by sorry
