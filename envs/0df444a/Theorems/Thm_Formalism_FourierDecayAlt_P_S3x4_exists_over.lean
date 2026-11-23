-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_exists_over
-- name    : Formalism.FourierDecayAlt.P.S3x4.exists_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:58.863768+00:00
-- url     : https://prove2.me/theorems/6aec4d4b-8dc1-4730-a52d-58c1fd96c29b
-- title:
--   S3x4: exists over
-- statement:
--   The S3x4 construction uses the exists over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L180-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SplitFrameTransitive.lean#L180-L232

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
variable {V A A' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup A] [Module K A]
  [AddCommGroup A'] [Module K A']

theorem Formalism.FourierDecayAlt.P.S3x4.exists_over [FiniteDimensional K A'] (π : V →ₗ[K] A) (hπ : Function.Surjective π)
    (j j' : A' →ₗ[K] V) (hj : Function.Injective j) (hj' : Function.Injective j')
    (hjj : π ∘ₗ j = π ∘ₗ j') :
    ∃ h : V →ₗ[K] V, Function.Injective h ∧ π ∘ₗ h = π ∧ h ∘ₗ j' = j := by sorry
