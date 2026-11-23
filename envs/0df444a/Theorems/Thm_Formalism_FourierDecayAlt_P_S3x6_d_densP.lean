-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_densP
-- name    : Formalism.FourierDecayAlt.P.S3x6.d_densP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:59.560337+00:00
-- url     : https://prove2.me/theorems/6bc5ad81-63b3-41d1-a0f3-873fd1d02eea
-- title:
--   S3x6: d dens P
-- statement:
--   The S3x6 construction uses the d dens P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L816-L830
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L816-L830

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

theorem Formalism.FourierDecayAlt.P.S3x6.d_densP (η : ℤ) (q b : ℕ) :
    densP η q 1 b = ∏ i ∈ Finset.range b, (1 - (η : ℝ) ^ (i + 1) * ((q : ℝ) ^ (i + 1))⁻¹) := by sorry
