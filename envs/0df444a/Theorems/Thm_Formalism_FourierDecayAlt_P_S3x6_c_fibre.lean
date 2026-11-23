-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_fibre
-- name    : Formalism.FourierDecayAlt.P.S3x6.c_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:52.53075+00:00
-- url     : https://prove2.me/theorems/1587218a-8dac-4e0c-87d9-8c048c079eb0
-- title:
--   S3x6: c fibre
-- statement:
--   The S3x6 construction uses the c fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L532-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L532-L576

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

theorem Formalism.FourierDecayAlt.P.S3x6.c_fibre [DecidableEq K] (hq : Fintype.card K = q ^ 2) (c : K) (hc : c ^ q = c) (hc0 : c ≠ 0) :
    (univ.filter (fun x : K => x ^ (q + 1) = c)).card = q + 1 := by sorry
