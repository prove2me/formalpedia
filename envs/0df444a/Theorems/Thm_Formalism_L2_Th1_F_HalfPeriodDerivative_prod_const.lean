-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_prod_const
-- name    : Formalism.L2.Th1.F.HalfPeriodDerivative.prod_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:45.18845+00:00
-- url     : https://prove2.me/theorems/a524fd60-f491-42ba-b6f4-890a7082b9c0
-- title:
--   Half Period Derivative: prod const
-- statement:
--   The Half Period Derivative construction uses the prod const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L52-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/WeierstrassPSecondDerivative.lean#L52-L79

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.HalfPeriodDerivative

theorem Formalism.L2.Th1.F.HalfPeriodDerivative.prod_const (ha : SigmaAdd) (hq : SigmaQuasi) (hz : SigmaZero) (L : PeriodPair) {t z : ℂ}
    (ht : t ∉ L.lattice) (h2 : 2 * t ∈ L.lattice) (hzL : z ∉ L.lattice) (hzt : z + t ∉ L.lattice) :
    (L.weierstrassP (z + t) - L.weierstrassP t) * (L.weierstrassP z - L.weierstrassP t)
      * wSigma L t ^ 4 = Complex.exp (wEta L (2 * t) * t) := by sorry
