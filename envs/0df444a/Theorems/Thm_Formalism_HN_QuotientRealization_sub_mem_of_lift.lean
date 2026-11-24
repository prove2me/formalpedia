-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_sub_mem_of_lift
-- name    : Formalism.HN.QuotientRealization.sub_mem_of_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:06.00681+00:00
-- url     : https://prove2.me/theorems/5cfa214a-050f-4f15-a507-c7eaf1b5e269
-- title:
--   Quotient Realization: sub mem of lift
-- statement:
--   The Quotient Realization construction uses the sub mem of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L330-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L330-L336

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
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
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)

theorem Formalism.HN.QuotientRealization.sub_mem_of_lift (hc : ∀ k, U.mkQ (c k) = b'' k) (x : V) :
    x - ∑ k, b''.repr (U.mkQ x) k • c k ∈ U := by sorry
