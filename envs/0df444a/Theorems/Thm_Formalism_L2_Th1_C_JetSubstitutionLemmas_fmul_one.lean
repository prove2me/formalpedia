-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_fmul_one
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.fmul_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:21.143816+00:00
-- url     : https://prove2.me/theorems/2993bb2e-aefa-4a42-9d77-f315d908cda1
-- title:
--   Jet Substitution Lemmas: fmul one
-- statement:
--   The Jet Substitution Lemmas construction uses the fmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L355-L358

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
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
open JetSubstitutionLemmas
open Formalism.L2.Th1.C.JetSubstitutionLemmas
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.fmul_one {l linv : PowerSeries K} (h : IsLogPair l linv) {w : MvPowerSeries σ K}
    (hw : MvPowerSeries.constantCoeff w = 0) : fmul l linv 1 w = w := by sorry
