-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_key_lemma
-- name    : Formalism.HN.DualPolygon.key_lemma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:26:33.315545+00:00
-- url     : https://prove2.me/theorems/1cd71a32-cbfb-45eb-a347-1f6ecb675aef
-- title:
--   Dual Polygon: key lemma
-- statement:
--   The Dual Polygon construction uses the key lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L863-L996
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L863-L996

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem Formalism.HN.DualPolygon.key_lemma (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V)
    (hN : IsSat (Formalism.HermitianLatticesTheory.realize b X) A N) :
    rkK (dualLat A ⊓ annO N) + rkK N = finrank K V ∧
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N)) *
              Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) A) *
              2 ^ (finrank ℚ K * rkK (dualLat A ⊓ annO N)) =
      |(NumberField.discr K : ℝ)| ^ rkK (dualLat A ⊓ annO N) *
        Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) := by sorry
