-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_two_le
-- name    : Formalism.FourierDecayAlt.P.S3x6.c_two_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:51.034672+00:00
-- url     : https://prove2.me/theorems/0ddb91f8-9296-460e-af95-8eb3c1fa4de4
-- title:
--   S3x6: c two le
-- statement:
--   The S3x6 construction uses the c two le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L504-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L504-L508

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
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)

theorem Formalism.FourierDecayAlt.P.S3x6.c_two_le (hq : Fintype.card K = q ^ 2) : 2 ≤ q := by sorry
