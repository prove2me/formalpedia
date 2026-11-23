-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_fibre
-- name    : Formalism.FourierDecayAlt.P.S3x4.card_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:42.61828+00:00
-- url     : https://prove2.me/theorems/87ba15c5-ff7b-4ab3-b9bb-2cb8bf771d2c
-- title:
--   S3x4: card fibre
-- statement:
--   The S3x4 construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L278-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L278-L308

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type} [Field K]

theorem Formalism.FourierDecayAlt.P.S3x4.card_fibre [Fintype K] (n a : ℕ) (R : Matrix (Fin a) (Fin a) K)
    (X₁ : Matrix (Fin n) (Fin a) K) (hX : X₁.rank = a) :
    Nat.card {X₂ : Matrix (Fin n) (Fin a) K // X₂.rank = a ∧ X₂ᵀ * X₁ = Rᵀ} =
      Fintype.card K ^ ((n - a) * R.rank) *
        ∏ j ∈ range (a - R.rank), (Fintype.card K ^ (n - a) - Fintype.card K ^ j) := by sorry
