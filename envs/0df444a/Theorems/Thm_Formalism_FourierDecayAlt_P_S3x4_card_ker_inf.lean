-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_card_ker_inf
-- name    : Formalism.FourierDecayAlt.P.S3x4.card_ker_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:38.841904+00:00
-- url     : https://prove2.me/theorems/aef570c4-0564-4847-b992-8de714adbb4a
-- title:
--   S3x4: card ker inf
-- statement:
--   The S3x4 construction uses the card ker inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L80-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L80-L123

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

theorem Formalism.FourierDecayAlt.P.S3x4.card_ker_inf [Fintype K] {A B : Type*} (U : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup U] [Module K U] [Finite A] [Finite U]
    (R : A →ₗ[K] B) :
    Nat.card {Y : A →ₗ[K] U // LinearMap.ker R ⊓ LinearMap.ker Y = ⊥} =
      Fintype.card K ^ (finrank K U * finrank K (LinearMap.range R)) *
      ∏ j ∈ range (finrank K (LinearMap.ker R)),
        (Fintype.card K ^ finrank K U - Fintype.card K ^ j) := by sorry
