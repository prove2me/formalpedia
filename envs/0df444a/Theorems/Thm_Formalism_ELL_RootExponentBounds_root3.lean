-- Prove2me | Theorems.Thm_Formalism_ELL_RootExponentBounds_root3
-- name    : Formalism.ELL.RootExponentBounds.root3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:01.931042+00:00
-- url     : https://prove2.me/theorems/3707e5c9-db29-4e54-91d6-af8694c5ba0e
-- title:
--   Root Exponent Bounds: root3
-- statement:
--   The Root Exponent Bounds construction uses the root3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L33-L42

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

theorem Formalism.ELL.RootExponentBounds.root3 {c a b d r : K} (hc : ‖c‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (h : c * r ^ 3 + a * r ^ 2 + b * r + d = 0) : ‖r‖ ≤ 1 := by sorry
