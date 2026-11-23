-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_injective
-- name    : Formalism.FourierDecayAlt.P.S3x4.card_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:33.015003+00:00
-- url     : https://prove2.me/theorems/3a113669-5ad9-4063-9079-709e23648262
-- title:
--   S3x4: card injective
-- statement:
--   The S3x4 construction uses the card injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L40-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L40-L69

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
variable {K : Type*} [Field K]

theorem Formalism.FourierDecayAlt.P.S3x4.card_injective [Fintype K] (W U : Type*) [AddCommGroup W] [Module K W] [AddCommGroup U]
    [Module K U] [Finite W] [Finite U] :
    Nat.card {f : W →ₗ[K] U // Function.Injective f} =
      ∏ j ∈ range (finrank K W), (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by sorry
