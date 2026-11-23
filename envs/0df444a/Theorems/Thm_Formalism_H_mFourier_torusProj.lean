-- Prove2me | Theorems.Thm_Formalism_H_mFourier_torusProj
-- name    : Formalism.H.mFourier_torusProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:42.372196+00:00
-- url     : https://prove2.me/theorems/08f53198-bc8f-4798-b165-883c4eb33ecd
-- title:
--   H: m Fourier torus Proj
-- statement:
--   The H construction uses the m Fourier torus Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/TorusProjIsOpenQuotientMap.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/TorusProjIsOpenQuotientMap.lean#L81-L95

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

theorem Formalism.H.mFourier_torusProj (e : Module.Basis ι ℝ V) (m : ι → ℤ) (t : ι → ℝ) :
    UnitAddTorus.mFourier m (torusProj ι t) =
      Complex.exp (2 * Real.pi * Complex.I * (⟪dualVec e m, e.equivFunL.symm t⟫ : ℝ)) := by sorry
