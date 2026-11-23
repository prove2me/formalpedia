-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_piece_eq_map
-- name    : Formalism.HN.PlaceDecomposition.piece_eq_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:02.920891+00:00
-- url     : https://prove2.me/theorems/ab02a578-8efa-4d54-affe-ce201b9e7f59
-- title:
--   Place Decomposition: piece eq map
-- statement:
--   The Place Decomposition construction uses the piece eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L431-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L431-L455

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
  [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace K)]

theorem Formalism.HN.PlaceDecomposition.piece_eq_map (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v =
      (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v) := by sorry
