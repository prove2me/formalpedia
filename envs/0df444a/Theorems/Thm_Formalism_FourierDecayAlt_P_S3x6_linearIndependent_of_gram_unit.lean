-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_linearIndependent_of_gram_unit
-- name    : Formalism.FourierDecayAlt.P.S3x6.linearIndependent_of_gram_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:25.691101+00:00
-- url     : https://prove2.me/theorems/8402972d-0a5c-44d8-b6a1-4ebc920c70d1
-- title:
--   S3x6: linear Independent of gram unit
-- statement:
--   The S3x6 construction uses the linear Independent of gram unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L255-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L255-L267

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

theorem Formalism.FourierDecayAlt.P.S3x6.linearIndependent_of_gram_unit (h : V →ₛₗ[σ] V →ₗ[K] K) {κ : Type} [Fintype κ] [DecidableEq κ] (z : κ → V)
    (hG : IsUnit (gramMatrix h z).det) : LinearIndependent K z := by sorry
