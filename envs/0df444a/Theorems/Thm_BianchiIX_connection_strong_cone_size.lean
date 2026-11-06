-- Prove2me | Theorems.Thm_BianchiIX_connection_strong_cone_size
-- name    : BianchiIX.connection_strong_cone_size
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T09:34:21.150168+00:00
-- url     : https://prove2.me/theorems/428a77df-da81-42a7-b015-ba9c0959e040
-- title:
--   Exponential contraction uniformly controls the strong cone row
-- statement:
--   Let $\mu\geq4$, $0\leq\varepsilon\leq1$, $0<u\leq\varepsilon/\mu$,
--   $0<w\leq\varepsilon$, $L\geq1$ and $w=e^{-L}$. Then
--   $$\sqrt u\,e^{-\mu L/4}
--   \left(274L+9000(1/u+L/\mu)\sqrt u+32\mu\sqrt w/w\right)
--   \leq20000\sqrt\varepsilon.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/ConnectionConeSize.lean#L37-L95

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.connection_strong_cone_size {μ ε u w L : ℝ} (hμ : 4 ≤ μ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 < u ∧ u ≤ ε / μ) (hw : 0 < w ∧ w ≤ ε) (hL : 1 ≤ L) (hwexp : w = Real.exp (-L)) :
    (Real.sqrt u * Real.exp (-μ * L / 4)) *
      (274 * L + 9000 * (1 / u + L / μ) * Real.sqrt u + 32 * μ / w * Real.sqrt w) ≤ 20000 * Real.sqrt ε := by sorry
