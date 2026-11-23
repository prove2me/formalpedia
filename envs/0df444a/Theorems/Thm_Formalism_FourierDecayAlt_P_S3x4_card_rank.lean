-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_rank
-- name    : Formalism.FourierDecayAlt.P.S3x4.card_rank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:43:13.759567+00:00
-- url     : https://prove2.me/theorems/aa7fe69a-ba23-4550-b48d-291fd6e9a5ca
-- title:
--   S3x4: card rank
-- statement:
--   The S3x4 construction uses the card rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L267-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L267-L276

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

theorem Formalism.FourierDecayAlt.P.S3x4.card_rank [Fintype K] (n a : ℕ) :
    Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a} =
      ∏ j ∈ range a, (Fintype.card K ^ n - Fintype.card K ^ j) := by sorry
