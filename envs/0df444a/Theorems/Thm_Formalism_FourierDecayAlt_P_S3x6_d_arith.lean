-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_arith
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_arith
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:44.78769+00:00
-- url     : https://prove2.me/theorems/07a5647b-4487-4d96-aad1-03f69b8e8df3
-- title:
--   S3x6: d arith
-- statement:
--   The S3x6 construction uses the d arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L832-L854
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L832-L854

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_arith (q : ℕ) (hq : 0 < q) (s : ℕ → ℕ)
    (hs : ∀ n, (q : ℤ) * s n = q ^ n * (q ^ n - (-1) ^ n)) (b : ℕ) :
    ((∏ j ∈ Finset.range b, s (j + 1) : ℕ) : ℝ) = (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b := by sorry
