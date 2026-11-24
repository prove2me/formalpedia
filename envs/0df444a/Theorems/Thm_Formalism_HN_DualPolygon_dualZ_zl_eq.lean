-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_dualZ_zl_eq
-- name    : Formalism.HN.DualPolygon.dualZ_zl_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:50.166809+00:00
-- url     : https://prove2.me/theorems/0ddfd0d4-450e-4242-8ad2-83a173364ded
-- title:
--   Dual Polygon: dual Z zl eq
-- statement:
--   The Dual Polygon construction uses the dual Z zl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L196-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L196-L310

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.HN.DualPolygon.dualZ_zl_eq [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (N : Submodule (𝓞 K) V) :
    dualZ (zl (Formalism.HermitianLatticesTheory.realize b X) A) ⊓
        ((Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ).restrictScalars ℤ =
      (zl (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (tdualLat A ⊓ annO N)).map
        (((2 : ℝ) • (cE : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ] _)).restrictScalars ℤ) := by sorry
