-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_monic_extract
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.monic_extract
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:57.045798+00:00
-- url     : https://prove2.me/theorems/7af45ce8-4b07-4358-86d1-9a151e9475c1
-- title:
--   Word Monic Extraction: monic extract
-- statement:
--   The Word Monic Extraction construction uses the monic extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L310-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L310-L321

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.monic_extract {V : Type} [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n : ℕ) (A₀ : R[X])
    (hA : A₀.Monic) (hn : A₀.natDegree = n) (y : Fin (n + 1) → ℝ) (hy : Function.Injective y)
    (x : M) : ∑ i, ((lagCo y i : ℝ) : ℂ) • ev (evR A₀ (y i) • x) = ev x := by sorry
