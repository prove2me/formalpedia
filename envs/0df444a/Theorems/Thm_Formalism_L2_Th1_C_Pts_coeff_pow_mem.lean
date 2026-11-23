-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_Pts_coeff_pow_mem
-- name    : Formalism.L2.Th1.C.Pts.coeff_pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:07.475863+00:00
-- url     : https://prove2.me/theorems/a5e6437e-98a9-4c16-9c17-10a215c3c45d
-- title:
--   Pts: coeff pow mem
-- statement:
--   The Pts construction uses the coeff pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L330-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/Points.lean#L330-L344

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Pts
open IntegralMvPolynomialLemmas
variable {K : Type} [Field K] {σ : Type} {R : Subring K} {l linv : PowerSeries K}

theorem Formalism.L2.Th1.C.Pts.coeff_pow_mem {i : PowerSeries K} {n : ℕ} (hi : ∀ m < n, PowerSeries.coeff m i ∈ R)
    (k : ℕ) : ∀ m < n, PowerSeries.coeff m (i ^ k) ∈ R := by sorry
