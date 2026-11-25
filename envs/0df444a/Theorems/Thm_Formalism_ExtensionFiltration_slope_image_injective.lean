-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_slope_image_injective
-- name    : Formalism.ExtensionFiltration.slope_image_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:19.558797+00:00
-- url     : https://prove2.me/theorems/eefac7c1-394c-4b59-a57e-499c5cc11df1
-- title:
--   Extension Filtration: slope image injective
-- statement:
--   The Extension Filtration construction uses the slope image injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentSlope.lean#L18-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/DescentSlope.lean#L18-L126

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
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

theorem Formalism.ExtensionFiltration.slope_image_injective
    {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hAfg : A.FG) (hA0 : A ≠ ⊥)
    (hinj : Function.Injective φ) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A ∧
      2 * slope (Formalism.HermitianLatticesTheory.realize b X) A - htMap b X b' X' φ ≤
        2 * slope (Formalism.HermitianLatticesTheory.realize b' X') (A.map (φ.restrictScalars (𝓞 K))) := by sorry
