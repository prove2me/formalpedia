-- Prove2me | Theorems.Thm_Formalism_ELL_RootExponentBounds_root2
-- name    : Formalism.ELL.RootExponentBounds.root2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:17.909661+00:00
-- url     : https://prove2.me/theorems/5fb3bc9d-179f-479b-82fe-0e595f1952bc
-- title:
--   Root Exponent Bounds: root2
-- statement:
--   The Root Exponent Bounds construction uses the root2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L23-L31

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

theorem Formalism.ELL.RootExponentBounds.root2 {a b r : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (h : r ^ 2 + a * r + b = 0) :
    ‖r‖ ≤ 1 := by sorry
