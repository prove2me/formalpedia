-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_restrict_orthogonal_complement_nondeg
-- name    : Formalism.FourierDecayAlt.P.S3x6.restrict_orthogonal_complement_nondeg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:12.127257+00:00
-- url     : https://prove2.me/theorems/8b3be152-ac50-4b74-92d7-aed406fdd41f
-- title:
--   S3x6: restrict orthogonal complement nondeg
-- statement:
--   The S3x6 construction uses the restrict orthogonal complement nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L34-L49

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

theorem Formalism.FourierDecayAlt.P.S3x6.restrict_orthogonal_complement_nondeg {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) (hn : Nondeg h) (v : V)
    (hv : h v v = 1) : Nondeg (restrictFormAlt h (LinearMap.ker (h v))) := by sorry
