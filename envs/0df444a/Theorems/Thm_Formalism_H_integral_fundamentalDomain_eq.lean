-- Prove2me | Theorems.Thm_Formalism_H_integral_fundamentalDomain_eq
-- name    : Formalism.H.integral_fundamentalDomain_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:19.047794+00:00
-- url     : https://prove2.me/theorems/f613e1e0-31a1-48d1-a79e-4d152a9c8a01
-- title:
--   H: integral fundamental Domain eq
-- statement:
--   The H construction uses the integral fundamental Domain eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/FundamentalDomainEqPreimage.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/FundamentalDomainEqPreimage.lean#L25-L44

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_FundamentalDomainEqPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

theorem Formalism.H.integral_fundamentalDomain_eq (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by sorry
