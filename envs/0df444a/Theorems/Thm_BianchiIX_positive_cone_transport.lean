-- Prove2me | Theorems.Thm_BianchiIX_positive_cone_transport
-- name    : BianchiIX.positive_cone_transport
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:03:21.138296+00:00
-- url     : https://prove2.me/theorems/fa231561-4068-411f-9013-a546fc0e5cf4
-- title:
--   Positive radial normalization transports cones and adds logarithmic distortion
-- statement:
--   Let $D:\mathbb R^3\to\mathbb R^3$ be linear, $a,b\in\mathbb R^2$,
--   and $L\in\mathbb R$. Assume every $z$ with $z_0=1$ and
--   $|z_{i+1}|\leq a_i$ satisfies
--   $$(Dz)_0>0,\quad |\log(Dz)_0|\leq L,\quad
--   |(Dz)_{i+1}|\leq b_i(Dz)_0\quad(i=0,1).$$
--   If $w_0>0$ and $|w_{i+1}|\leq a_iw_0$, then
--   $$(Dw)_0>0,\quad |\log(Dw)_0|\leq|\log w_0|+L,\quad
--   |(Dw)_{i+1}|\leq b_i(Dw)_0\quad(i=0,1).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/PositiveConeTransport.lean#L8-L37

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.positive_cone_transport (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    {w : Fin 3 → ℝ} {a b : Fin 2 → ℝ} {L : ℝ} (hw0 : 0 < w 0)
    (hw : ∀ i : Fin 2, |w i.succ| ≤ a i * w 0)
    (H : ∀ z : Fin 3 → ℝ, z 0 = 1 → (∀ i : Fin 2, |z i.succ| ≤ a i) →
      0 < D z 0 ∧ |Real.log (D z 0)| ≤ L ∧ ∀ i : Fin 2, |D z i.succ| ≤ b i * D z 0) :
    0 < D w 0 ∧ |Real.log (D w 0)| ≤ |Real.log (w 0)| + L ∧
      ∀ i : Fin 2, |D w i.succ| ≤ b i * D w 0 := by sorry
