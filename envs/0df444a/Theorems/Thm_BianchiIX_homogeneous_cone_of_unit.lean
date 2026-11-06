-- Prove2me | Theorems.Thm_BianchiIX_homogeneous_cone_of_unit
-- name    : BianchiIX.homogeneous_cone_of_unit
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:54:30.196305+00:00
-- url     : https://prove2.me/theorems/57a0e59c-25ec-44f8-923e-f6c9c0171c22
-- title:
--   Unit radial cone estimates extend to both orientations and the vertex
-- statement:
--   Let $D:\mathbb R^3\to\mathbb R^3$ be linear and $R>0$.
--   Suppose every $z$ with $Rz_0=1$, $|z_1|\leq a$, $|z_2|\leq b$
--   satisfies $(Dz)_0\geq0$, $|(Dz)_1|\leq A(Dz)_0$, and
--   $|(Dz)_2|\leq B(Dz)_0$. Then every $v$ satisfying
--   $|v_1|\leq a|Rv_0|$, $|v_2|\leq b|Rv_0|$ obeys
--   $$|(Dv)_1|\leq A|(Dv)_0|,\qquad |(Dv)_2|\leq B|(Dv)_0|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/HomogeneousCone.lean#L9-L48

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.homogeneous_cone_of_unit
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {R a b A B : ℝ} (hR : 0 < R)
    (hunit : ∀ z : Fin 3 → ℝ, R * z 0 = 1 → |z 1| ≤ a → |z 2| ≤ b →
      0 ≤ D z 0 ∧ |D z 1| ≤ A * D z 0 ∧ |D z 2| ≤ B * D z 0)
    (v : Fin 3 → ℝ) (hva : |v 1| ≤ a * |R * v 0|) (hvb : |v 2| ≤ b * |R * v 0|) :
    |D v 1| ≤ A * |D v 0| ∧ |D v 2| ≤ B * |D v 0| := by sorry
