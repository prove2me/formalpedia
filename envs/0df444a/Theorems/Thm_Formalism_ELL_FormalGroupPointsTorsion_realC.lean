-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_realC
-- name    : Formalism.ELL.FormalGroupPointsTorsion.realC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:45.82055+00:00
-- url     : https://prove2.me/theorems/66c28f13-9a26-49b1-af7c-f047e11ee326
-- title:
--   Formal Group Points Torsion: real C
-- statement:
--   The Formal Group Points Torsion construction uses the real C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L115-L122

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}

theorem Formalism.ELL.FormalGroupPointsTorsion.realC {L V M : ℝ} (hL0 : 0 ≤ L) (hV0 : 0 ≤ V) (hLM : L ^ 2 ≤ M) (hM : 1 ≤ M)
    (hV : V ≤ max 1 L) : L ≤ M ∧ V ≤ M ∧ L * V ≤ M := by sorry
