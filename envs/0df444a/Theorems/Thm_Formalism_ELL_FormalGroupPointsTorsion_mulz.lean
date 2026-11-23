-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_mulz
-- name    : Formalism.ELL.FormalGroupPointsTorsion.mulz
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:35.296097+00:00
-- url     : https://prove2.me/theorems/c98f6cc6-003c-4598-aafb-1f43c7de87f9
-- title:
--   Formal Group Points Torsion: mulz
-- statement:
--   The Formal Group Points Torsion construction uses the mulz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L404-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L404-L434

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

theorem Formalism.ELL.FormalGroupPointsTorsion.mulz [DecidableEq K] (hW : IntegralModel W) (P : W.toAffine.Point) (hP : InFormalGroupPoints P)
    (hP0 : P ≠ 0) (k : ℕ) :
    InFormalGroupPoints ((k + 1) • P) ∧ ‖zf ((k + 1) • P) - ((k + 1 : ℕ) : K) * zf P‖ < ‖zf P‖ := by sorry
