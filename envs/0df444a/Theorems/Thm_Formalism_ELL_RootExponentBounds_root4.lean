-- Prove2me | Theorems.Thm_Formalism_ELL_RootExponentBounds_root4
-- name    : Formalism.ELL.RootExponentBounds.root4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:49.033512+00:00
-- url     : https://prove2.me/theorems/792e8ef5-5e8b-48c3-91dd-03b01c537b7c
-- title:
--   Root Exponent Bounds: root4
-- statement:
--   The Root Exponent Bounds construction uses the root4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L44-L54

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.RootExponentBounds.root4 {c a b d e r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (he : ‖e‖ ≤ 1) (h : c * r ^ 4 + a * r ^ 3 + b * r ^ 2 + d * r + e = 0) : ‖r‖ ≤ 1 := by sorry
