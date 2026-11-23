-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_bigx3
-- name    : Formalism.ELL.FormalGroupPointsTorsion.bigx3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:36.5778+00:00
-- url     : https://prove2.me/theorems/ea401135-0cc2-4ee6-8fd3-69f0be6f32d0
-- title:
--   Formal Group Points Torsion: bigx3
-- statement:
--   The Formal Group Points Torsion construction uses the bigx3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L124-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L124-L179

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

theorem Formalism.ELL.FormalGroupPointsTorsion.bigx3 (hW : IntegralModel W) {x1 x2 x3 y3 l v : K} (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖)
    (h3 : W.toAffine.Equation x3 y3) (hy3 : y3 = l * x3 + v)
    (e1 : l ^ 2 + W.a₁ * l - W.a₂ = x1 + x2 + x3)
    (e2 : W.a₄ - 2 * l * v - W.a₁ * v - W.a₃ * l = x1 * x2 + x3 * (x1 + x2)) : 1 < ‖x3‖ := by sorry
