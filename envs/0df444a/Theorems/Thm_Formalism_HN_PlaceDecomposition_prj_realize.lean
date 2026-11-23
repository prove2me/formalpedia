-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_realize
-- name    : Formalism.HN.PlaceDecomposition.prj_realize
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:11.421658+00:00
-- url     : https://prove2.me/theorems/c7c5b84f-06a3-4f44-8d2e-660f20869334
-- title:
--   Place Decomposition: prj realize
-- statement:
--   The Place Decomposition construction uses the prj realize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L229-L233

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

theorem Formalism.HN.PlaceDecomposition.prj_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : prj v (Formalism.HermitianLatticesTheory.realize b X x) = psi v (Formalism.HermitianLatticesTheory.fcoord b X v x) := by sorry
