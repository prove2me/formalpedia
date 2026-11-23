-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_key
-- name    : Formalism.ELL.FormalGroupPointsTorsion.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:05.478822+00:00
-- url     : https://prove2.me/theorems/da918aa0-b9fc-4795-9368-5246f10454c8
-- title:
--   Formal Group Points Torsion: key
-- statement:
--   The Formal Group Points Torsion construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L370-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L370-L402

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

theorem Formalism.ELL.FormalGroupPointsTorsion.key [DecidableEq K] (hW : IntegralModel W) (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hQ : InFormalGroupPoints Q) (hne : P ≠ 0 ∨ Q ≠ 0) :
    InFormalGroupPoints (P + Q) ∧ ‖zf (P + Q) - zf P - zf Q‖ < max ‖zf P‖ ‖zf Q‖ := by sorry
