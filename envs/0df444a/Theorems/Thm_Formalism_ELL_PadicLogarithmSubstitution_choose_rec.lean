-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_choose_rec
-- name    : Formalism.ELL.PadicLogarithmSubstitution.choose_rec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:29.328827+00:00
-- url     : https://prove2.me/theorems/dff05f30-5579-4b80-bb95-5e2bdcf3985a
-- title:
--   Padic Logarithm Substitution: choose rec
-- statement:
--   The Padic Logarithm Substitution construction uses the choose rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L107-L113

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable (p : ℕ) [Fact p.Prime] (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]

theorem Formalism.ELL.PadicLogarithmSubstitution.choose_rec (b : ℤ_[p]) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ_[p]) * Ring.choose b (n + 1) = (b - n) * Ring.choose b n := by sorry
