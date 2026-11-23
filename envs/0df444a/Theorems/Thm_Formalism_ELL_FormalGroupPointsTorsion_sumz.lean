-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_sumz
-- name    : Formalism.ELL.FormalGroupPointsTorsion.sumz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:39.562583+00:00
-- url     : https://prove2.me/theorems/a9827a66-3a05-4f03-9dfa-48ddd8134a72
-- title:
--   Formal Group Points Torsion: sumz
-- statement:
--   The Formal Group Points Torsion construction uses the sumz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L207-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L207-L305

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

theorem Formalism.ELL.FormalGroupPointsTorsion.sumz (hW : IntegralModel W) {x1 x2 x3 y1 y2 y3 l v : K}
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hX3 : 1 < ‖x3‖)
    (hE1 : W.toAffine.Equation x1 y1) (hE2 : W.toAffine.Equation x2 y2)
    (hE3 : W.toAffine.Equation x3 y3)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e3 : v ^ 2 + W.a₃ * v - W.a₆ = x1 * x2 * x3)
    (hN : x1 * y2 * y3 + x2 * y1 * y3 + x3 * y1 * y2 =
      -(W.a₁ * (l * v ^ 2)) - W.a₂ * v ^ 2 + W.a₃ * (l ^ 2 * v) + (2 * W.a₄) * (l * v)
        - (3 * W.a₆) * l ^ 2) :
    ‖x1 / y1 + x2 / y2 + x3 / y3‖ < max ‖x1 / y1‖ ‖x2 / y2‖ := by sorry
