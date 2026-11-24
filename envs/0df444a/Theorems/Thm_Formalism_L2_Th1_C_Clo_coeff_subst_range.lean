-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Clo_coeff_subst_range
-- name    : Formalism.L2.Th1.C.Clo.coeff_subst_range
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:01.56329+00:00
-- url     : https://prove2.me/theorems/4ea550e5-5063-4696-9ebd-5848f8358e58
-- title:
--   Clo: coeff subst range
-- statement:
--   The Clo construction uses the coeff subst range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Closure.lean#L21-L34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormClosed
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Closure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Clo
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.Th1.C.Clo.coeff_subst_range {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (g : PowerSeries K) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst f g) =
      ∑ k ∈ range (n.degree + 1), PowerSeries.coeff k g * MvPowerSeries.coeff n (f ^ k) := by sorry
