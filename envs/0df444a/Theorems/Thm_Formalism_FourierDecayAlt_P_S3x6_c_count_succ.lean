-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_c_count_succ
-- name    : Formalism.FourierDecayAlt.P.S3x6.c_count_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:25.428772+00:00
-- url     : https://prove2.me/theorems/612d594c-3a03-4d0a-8931-3ddc0ddc709c
-- title:
--   S3x6: c count succ
-- statement:
--   The S3x6 construction uses the c count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L634-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L634-L659

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

theorem Formalism.FourierDecayAlt.P.S3x6.c_count_succ [DecidableEq K] (n : ℕ) (c : K) :
    (univ.filter (fun w : Fin (n + 1) → K => ∑ i, w i ^ q * w i = c)).card =
      ∑ x : K, (univ.filter (fun w : Fin n → K => ∑ i, w i ^ q * w i = c - x ^ q * x)).card := by sorry
