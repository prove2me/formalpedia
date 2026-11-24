-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_span_complex
-- name    : Formalism.HN.PlaceDecomposition.finrank_span_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:41.509726+00:00
-- url     : https://prove2.me/theorems/4b1761b3-2930-4f36-80ac-a3f015c3ed0f
-- title:
--   Place Decomposition: finrank span complex
-- statement:
--   The Place Decomposition construction uses the finrank span complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L335-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L335-L415

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

theorem Formalism.HN.PlaceDecomposition.finrank_span_complex (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    finrank ℂ (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))) = rkK N := by sorry
