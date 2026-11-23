-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_osmul
-- name    : Formalism.HN.PlaceDecomposition.fcoord_osmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:58.045576+00:00
-- url     : https://prove2.me/theorems/18215ee7-819a-49bf-98e9-ec0e293e40cf
-- title:
--   Place Decomposition: fcoord osmul
-- statement:
--   The Place Decomposition construction uses the fcoord osmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L181-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L181-L185

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

theorem Formalism.HN.PlaceDecomposition.fcoord_osmul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : 𝓞 K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding (a : K) • Formalism.HermitianLatticesTheory.fcoord b X v x := by sorry
