-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_proj_eq_tv
-- name    : Formalism.HN.QuotientRealization.proj_eq_tv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:38.907803+00:00
-- url     : https://prove2.me/theorems/640d8d71-0120-4073-a0fd-43573fbf1c2e
-- title:
--   Quotient Realization: proj eq tv
-- statement:
--   The Quotient Realization construction uses the proj eq tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L338-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L338-L359

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

theorem Formalism.HN.QuotientRealization.proj_eq_tv (hc : ∀ k, U.mkQ (c k) = b'' k) (v : InfinitePlace K) (x : V) :
    (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x)) =
      tv b X U c v (fun k => v.embedding (b''.repr (U.mkQ x) k)) := by sorry
