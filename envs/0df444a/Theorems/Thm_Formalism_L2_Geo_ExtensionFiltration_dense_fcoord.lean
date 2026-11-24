-- Prove2me | Theorems.Thm_Formalism_L2_Geo_ExtensionFiltration_dense_fcoord
-- name    : Formalism.L2.Geo.ExtensionFiltration.dense_fcoord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:34.047052+00:00
-- url     : https://prove2.me/theorems/955a78b7-49ea-4d95-b5fe-74d1c0fbf999
-- title:
--   Extension Filtration: dense fcoord
-- statement:
--   The Extension Filtration construction uses the dense fcoord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/OperatorNormFibers/PDescentCutA.lean#L38-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/OperatorNormFibers/PDescentCutA.lean#L38-L66

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

theorem Formalism.L2.Geo.ExtensionFiltration.dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by sorry
