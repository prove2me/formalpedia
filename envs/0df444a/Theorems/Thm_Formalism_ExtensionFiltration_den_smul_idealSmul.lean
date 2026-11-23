-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_den_smul_idealSmul
-- name    : Formalism.ExtensionFiltration.den_smul_idealSmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:30.374058+00:00
-- url     : https://prove2.me/theorems/fdcdb951-a6ec-4169-b753-9ca70c330fb2
-- title:
--   Extension Filtration: den smul ideal Smul
-- statement:
--   The Extension Filtration construction uses the den smul ideal Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/TwistLower.lean#L63-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/TwistLower.lean#L63-L100

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
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
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
omit [StarRing K] [IsTotallyComplex K]

theorem Formalism.ExtensionFiltration.den_smul_idealSmul (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (M : Submodule (𝓞 K) V) :
    (Ideal.span {(I.den : 𝓞 K)}) • Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M = I.num • M := by sorry
