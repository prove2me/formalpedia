-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_sum_Xs
-- name    : Formalism.FourierDecayAlt.P.UnipotentSums.sum_Xs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:07:49.260702+00:00
-- url     : https://prove2.me/theorems/9c4cb0bf-9861-405d-a7d2-7b8d7b02523c
-- title:
--   Unipotent Sums: sum Xs
-- statement:
--   The Unipotent Sums construction uses the sum Xs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L40-L53

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.UnipotentSums.sum_Xs (g : Fin (2 * r + k + 1) → ℂ) (hg : ∀ p : Fin (2 * r + k + 1), p.val ≤ r + k → g p = 0) :
    ∑ p, g p = ∑ c : Fin r, g (esI k r c) := by sorry
