-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_takMap_symm
-- name    : Formalism.FourierDecayAlt.P.G9.takMap_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:27.436403+00:00
-- url     : https://prove2.me/theorems/521b8ee7-2e97-419b-8580-faaf7129591e
-- title:
--   G9: tak Map symm
-- statement:
--   The G9 construction uses the tak Map symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L127-L134

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem Formalism.FourierDecayAlt.P.G9.takMap_symm {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsSymm)
    (x y : EuclideanSpace ℂ (Fin d)) : ⟪takMap H x, y⟫_ℂ = ⟪takMap H y, x⟫_ℂ := by sorry
