-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_proj_norm_sq
-- name    : Formalism.HN.QuotientRealization.proj_norm_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:10.18173+00:00
-- url     : https://prove2.me/theorems/0aa757a9-08e5-4c7f-93a8-4e83ad052c6a
-- title:
--   Quotient Realization: proj norm sq
-- statement:
--   The Quotient Realization construction uses the proj norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L267-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L267-L319

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

theorem Formalism.HN.QuotientRealization.proj_norm_sq [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (x : V) :
    ‖(Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) S :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ.starProjection
        (Formalism.HermitianLatticesTheory.realize b X x)‖ ^ 2 =
      ∑ v, ‖(pv b X (Submodule.span K (S : Set V)) v)ᗮ.starProjection
        (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))‖ ^ 2 := by sorry
