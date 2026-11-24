-- Prove2me | Theorems.Thm_Formalism_H_fundamentalDomain_eq_preimage
-- name    : Formalism.H.fundamentalDomain_eq_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:13.606324+00:00
-- url     : https://prove2.me/theorems/dc15ecb5-f041-4bbf-b766-abf5fecae6c5
-- title:
--   H: fundamental Domain eq preimage
-- statement:
--   The H construction uses the fundamental Domain eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/FundamentalDomainEqPreimage.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeTheta/LatticeThetaProofs/FundamentalDomainEqPreimage.lean#L20-L23

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

theorem Formalism.H.fundamentalDomain_eq_preimage (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by sorry
