-- Prove2me | Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
-- name    : Formalism.ELL.SubstitutionCoefficientCongruence.integral_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:34.14381+00:00
-- url     : https://prove2.me/theorems/7322a9d9-f964-4ee7-b459-4e66f58339e7
-- title:
--   Substitution Coefficient Congruence: integral mul
-- statement:
--   The Substitution Coefficient Congruence construction uses the integral mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/NDeriv.lean#L108-L114

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

theorem Formalism.ELL.SubstitutionCoefficientCongruence.integral_mul {F G : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F)
    (hG : Formalism.G.IntegralMv G) : Formalism.G.IntegralMv (F * G) := by sorry
