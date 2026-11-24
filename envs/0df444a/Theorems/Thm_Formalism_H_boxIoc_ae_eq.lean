-- Prove2me | Theorems.Thm_Formalism_H_boxIoc_ae_eq
-- name    : Formalism.H.boxIoc_ae_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:47.1558+00:00
-- url     : https://prove2.me/theorems/d3ffeffb-0e74-4907-b577-4a6f47010f8e
-- title:
--   H: box Ioc ae eq
-- statement:
--   The H construction uses the box Ioc ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/TorusProjIsOpenQuotientMap.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/TorusProjIsOpenQuotientMap.lean#L97-L106

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_TorusProjIsOpenQuotientMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.H.boxIoc_ae_eq :
    ({x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} : Set (ι → ℝ))
      =ᵐ[volume] boxIco ι := by sorry
