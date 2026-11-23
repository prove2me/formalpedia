-- Prove2me | Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_pderiv
-- name    : Formalism.ELL.SubstitutionCoefficientCongruence.integral_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:57.282797+00:00
-- url     : https://prove2.me/theorems/82f9d3e4-4d89-4d94-9c8e-a99a97292ebc
-- title:
--   Substitution Coefficient Congruence: integral pderiv
-- statement:
--   The Substitution Coefficient Congruence construction uses the integral pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L122-L127

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}

theorem Formalism.ELL.SubstitutionCoefficientCongruence.integral_pderiv {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (i : σ) :
    Formalism.G.IntegralMv (MvPowerSeries.pderiv K i F) := by sorry
