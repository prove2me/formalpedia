-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_pderiv_Q
-- name    : Formalism.L2.Th1.C.JetSubstitutionLemmas.cc_pderiv_Q
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:57.511017+00:00
-- url     : https://prove2.me/theorems/299cd705-218c-4a22-b935-459257a28317
-- title:
--   Jet Substitution Lemmas: cc pderiv Q
-- statement:
--   The Jet Substitution Lemmas construction uses the cc pderiv Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L291-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/IntPSDerivativeOfLG.lean#L291-L333

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

theorem Formalism.L2.Th1.C.JetSubstitutionLemmas.cc_pderiv_Q {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (hl1 : PowerSeries.constantCoeff (PowerSeries.derivative K l) = 1) (ψ : PowerSeries K)
    (α β : K) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 0 (MvPowerSeries.pderiv K 1 (Q l ψ α β))) =
      α * β * PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K ψ)) := by sorry
