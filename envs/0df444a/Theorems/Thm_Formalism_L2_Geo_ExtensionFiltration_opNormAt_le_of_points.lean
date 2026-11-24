-- Prove2me | Theorems.Thm_Formalism_L2_Geo_ExtensionFiltration_opNormAt_le_of_points
-- name    : Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:53.970652+00:00
-- url     : https://prove2.me/theorems/f4570b74-30e3-4943-9930-164b0c9ae104
-- title:
--   Extension Filtration: op Norm At le of points
-- statement:
--   The Extension Filtration construction uses the op Norm At le of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/OperatorNormFibers/PDescentCutA.lean#L77-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/OperatorNormFibers/PDescentCutA.lean#L77-L103

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_OperatorNormFibers_PDescentCutA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.deprecated false
open Module NumberField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.ExtensionFiltration

theorem Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] W) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b' X' v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b' X' v φ ≤ C := by sorry
