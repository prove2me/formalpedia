-- Prove2me | Theorems.Thm_Formalism_ZF_landauLocal_logDeriv_prod
-- name    : Formalism.ZF.landauLocal_logDeriv_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:11.655863+00:00
-- url     : https://prove2.me/theorems/02c6ca79-75f6-4620-967e-760b41ece62d
-- title:
--   ZF: landau Local log Deriv prod
-- statement:
--   The ZF construction uses the landau Local log Deriv prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LandauLocalOf.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LandauLocalOf.lean#L44-L50

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by sorry
