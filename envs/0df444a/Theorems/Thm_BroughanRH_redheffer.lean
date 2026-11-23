-- Prove2me | Theorems.Thm_BroughanRH_redheffer
-- name    : BroughanRH.redheffer
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:19:32.012416+00:00
-- url     : https://prove2.me/theorems/2a1b4213-853b-471a-a4cf-7ec5d02463b5
-- title:
--   Redheffer’s determinant bound
-- statement:
--   For the one-based Redheffer matrix, its determinant is $O_\varepsilon(n^{1/2+\varepsilon})$ for every $\varepsilon>0$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 10.9. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem redheffer :
    let A (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun n => (A n).det) (fun n : ℕ => (n : ℝ) ^ (1/2 + ε)) := by sorry

end BroughanRH
