-- Prove2me | Theorems.Thm_Formalism_L2_Th1_A_Nn_X_pow_succ_dvd_of_derivative
-- name    : Formalism.L2.Th1.A.Nn.X_pow_succ_dvd_of_derivative
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:01.051708+00:00
-- url     : https://prove2.me/theorems/3554a981-0cd3-5cf0-91aa-702033935ac5
-- title:
--   Nn: X pow succ dvd of derivative
-- statement:
--   The Nn construction uses the X pow succ dvd of derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/XPowSuccDvdOfDerivative.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/XPowSuccDvdOfDerivative.lean#L18-L29

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Nn
variable {R : Type u} [CommRing R]

theorem Formalism.L2.Th1.A.Nn.X_pow_succ_dvd_of_derivative
    (hR : ∀ (n : ℕ) (r : R), n ≠ 0 → (n : R) * r = 0 → r = 0) {f : R⟦X⟧} {n : ℕ}
    (h0 : constantCoeff f = 0) (h : X ^ n ∣ derivative R f) : X ^ (n + 1) ∣ f := by sorry
