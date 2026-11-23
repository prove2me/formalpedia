-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_card_norm_one
-- name    : Formalism.FourierDecayAlt.P.S3x6.card_norm_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:42.876033+00:00
-- url     : https://prove2.me/theorems/bc63314c-8207-4caa-9ee8-b5db5f7b96de
-- title:
--   S3x6: card norm one
-- statement:
--   The S3x6 construction uses the card norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L711-L716
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean#L711-L716

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

theorem Formalism.FourierDecayAlt.P.S3x6.card_norm_one (hq : Fintype.card K = q ^ 2) (n : ℕ) :
    (q : ℤ) * Nat.card {w : Fin n → K // ∑ i, (w i) ^ q * w i = 1} = q ^ n * (q ^ n - (-1) ^ n) := by sorry
