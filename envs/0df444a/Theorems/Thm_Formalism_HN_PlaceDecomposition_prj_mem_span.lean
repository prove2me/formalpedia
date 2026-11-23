-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_mem_span
-- name    : Formalism.HN.PlaceDecomposition.prj_mem_span
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:06.193872+00:00
-- url     : https://prove2.me/theorems/13b5320f-41e4-492c-9045-03807f3b963f
-- title:
--   Place Decomposition: prj mem span
-- statement:
--   The Place Decomposition construction uses the prj mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L254-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L254-L275

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
variable [DecidableEq (InfinitePlace K)]

theorem Formalism.HN.PlaceDecomposition.prj_mem_span (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (hw : w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) :
    prj v w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by sorry
