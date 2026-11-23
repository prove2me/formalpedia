-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_equiv_comp
-- name    : Formalism.FourierDecayAlt.P.S3x4.exists_equiv_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:29.714835+00:00
-- url     : https://prove2.me/theorems/3c05c546-d274-4fa2-b19a-0832333cf18a
-- title:
--   S3x4: exists equiv comp
-- statement:
--   The S3x4 construction uses the exists equiv comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L9-L20

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

theorem Formalism.FourierDecayAlt.P.S3x4.exists_equiv_comp {A V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
    [FiniteDimensional K A] (i i' : A →ₗ[K] V) (hi : Function.Injective i)
    (hi' : Function.Injective i') : ∃ g : V ≃ₗ[K] V, ∀ x, g (i x) = i' x := by sorry
