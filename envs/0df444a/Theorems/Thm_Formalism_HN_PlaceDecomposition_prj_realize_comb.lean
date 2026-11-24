-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_realize_comb
-- name    : Formalism.HN.PlaceDecomposition.prj_realize_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:21.329553+00:00
-- url     : https://prove2.me/theorems/02aa923a-cfcc-4146-b37d-be26a144e4a3
-- title:
--   Place Decomposition: prj realize comb
-- statement:
--   The Place Decomposition construction uses the prj realize comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L235-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L235-L252

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

theorem Formalism.HN.PlaceDecomposition.prj_realize_comb (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
    (hr : ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = if u = v then 1 else 0)
    (x : V) :
    prj v (Formalism.HermitianLatticesTheory.realize b X x) =
      ∑ k, r k • Formalism.HermitianLatticesTheory.realize b X ((RingOfIntegers.basis K k : 𝓞 K) • x) := by sorry
