-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_dense_comb
-- name    : Formalism.HN.PlaceDecomposition.dense_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:00.722554+00:00
-- url     : https://prove2.me/theorems/f1b61307-db95-47db-b224-0251803c9ba4
-- title:
--   Place Decomposition: dense comb
-- statement:
--   The Place Decomposition construction uses the dense comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L12-L33

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

theorem Formalism.HN.PlaceDecomposition.dense_comb (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (t : InfinitePlace K → ℂ) :
    ∃ r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = t u := by sorry
