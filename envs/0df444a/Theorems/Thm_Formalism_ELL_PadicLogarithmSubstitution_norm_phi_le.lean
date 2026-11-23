-- Prove2me | Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_norm_phi_le
-- name    : Formalism.ELL.PadicLogarithmSubstitution.norm_phi_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:21.966798+00:00
-- url     : https://prove2.me/theorems/c8c6ee34-9a64-42b1-ad45-b9c3ade976f7
-- title:
--   Padic Logarithm Substitution: norm phi le
-- statement:
--   The Padic Logarithm Substitution construction uses the norm phi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntegralPSBserSubOne.lean#L133-L135

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

theorem Formalism.ELL.PadicLogarithmSubstitution.norm_phi_le (z : ℤ_[p]) : ‖phi p K z‖ ≤ 1 := by sorry
