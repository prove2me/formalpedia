-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_takMap_apply
-- name    : Formalism.FourierDecayAlt.P.G9.takMap_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:45.807877+00:00
-- url     : https://prove2.me/theorems/5a29c061-410d-4e7b-89cd-1b30b34acda4
-- title:
--   G9: tak Map apply
-- statement:
--   The G9 construction uses the tak Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L123-L125

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

theorem Formalism.FourierDecayAlt.P.G9.takMap_apply {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    takMap H x i = ∑ j, H i j * conj (x j) := by sorry
