-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_im_comb
-- name    : Formalism.HN.PlaceDecomposition.im_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:40.106413+00:00
-- url     : https://prove2.me/theorems/458cdbf3-1d7c-46b7-8b2e-7f3873b2287b
-- title:
--   Place Decomposition: im comb
-- statement:
--   The Place Decomposition construction uses the im comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L221-L225

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

theorem Formalism.HN.PlaceDecomposition.im_comb {κ : Type*} [Fintype κ] (r : κ → ℝ) (c : κ → ℂ) (f : ℂ) :
    ∑ k, r k * (c k * f).im = ((∑ k, (r k : ℂ) * c k) * f).im := by sorry
