-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_realize_mem
-- name    : Formalism.HN.PlaceDecomposition.realize_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:31.519926+00:00
-- url     : https://prove2.me/theorems/fc357ab7-e641-4b42-8165-87e5826ca8b3
-- title:
--   Place Decomposition: realize mem
-- statement:
--   The Place Decomposition construction uses the realize mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L206-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L206-L213

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.PlaceDecomposition.realize_mem (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V)
    {x : V} (hx : x ∈ N) :
    Formalism.HermitianLatticesTheory.realize b X x ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by sorry
