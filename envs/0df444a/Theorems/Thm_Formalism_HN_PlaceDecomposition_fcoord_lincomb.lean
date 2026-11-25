-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_lincomb
-- name    : Formalism.HN.PlaceDecomposition.fcoord_lincomb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:51.818909+00:00
-- url     : https://prove2.me/theorems/3344f70e-ce14-51b2-ab91-9a1fc65d241c
-- title:
--   Place Decomposition: fcoord lincomb
-- statement:
--   The Place Decomposition construction uses the fcoord lincomb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L187-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L187-L204

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

theorem Formalism.HN.PlaceDecomposition.fcoord_lincomb (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    {n : Type*} [Fintype n] (c : n → K) (y : n → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ k, c k • y k) = ∑ k, v.embedding (c k) • Formalism.HermitianLatticesTheory.fcoord b X v (y k) := by sorry
