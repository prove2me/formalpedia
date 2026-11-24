-- Prove2me | Theorems.Thm_Formalism_HN_DualPolygon_mu_dual
-- name    : Formalism.HN.DualPolygon.mu_dual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:44.939944+00:00
-- url     : https://prove2.me/theorems/a625e9e0-5486-4eb4-af30-bb97118856da
-- title:
--   Dual Polygon: mu dual
-- statement:
--   The Dual Polygon construction uses the mu dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L1481-L1510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DualPl.lean#L1481-L1510

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

theorem Formalism.HN.DualPolygon.mu_dual (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (hA0 : A ≠ ⊥) :
    muMax (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMin (Formalism.HermitianLatticesTheory.realize b X) A ∧
      muMin (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A) =
        (Real.log 2 - Real.log |(NumberField.discr K : ℝ)| / (finrank ℚ K : ℝ)) -
          muMax (Formalism.HermitianLatticesTheory.realize b X) A := by sorry
