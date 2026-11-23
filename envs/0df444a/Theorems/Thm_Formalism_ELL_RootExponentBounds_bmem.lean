-- Prove2me | Theorems.Thm_Formalism_ELL_RootExponentBounds_bmem
-- name    : Formalism.ELL.RootExponentBounds.bmem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:50.909162+00:00
-- url     : https://prove2.me/theorems/7a5dfab8-7119-4ac4-a726-d0fadee564af
-- title:
--   Root Exponent Bounds: bmem
-- statement:
--   The Root Exponent Bounds construction uses the bmem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/Change.lean#L70-L78

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

theorem Formalism.ELL.RootExponentBounds.bmem {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (h1 : W.a₁ ∈ unitBall K) (h2 : W.a₂ ∈ unitBall K) (h3 : W.a₃ ∈ unitBall K)
    (h4 : W.a₄ ∈ unitBall K) (h6 : W.a₆ ∈ unitBall K) :
    W.b₂ ∈ unitBall K ∧ W.b₄ ∈ unitBall K ∧ W.b₆ ∈ unitBall K ∧ W.b₈ ∈ unitBall K := by sorry
